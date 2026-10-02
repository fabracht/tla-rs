use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

use crate::ast::{Env, Expr, FairnessConstraint, State, Value};
use crate::eval::{Definitions, EvalError, eval};
use crate::graph::{LivenessGraph, StateGraph};

pub type Result<T> = std::result::Result<T, EvalError>;

#[derive(Debug, Clone)]
pub struct LivenessViolation {
    pub prefix: Vec<State>,
    pub cycle: Vec<State>,
    pub property: String,
    pub fairness_info: Vec<(String, bool)>,
}

/// A counterexample as graph state indices. `prefix` runs from an initial state to
/// `cycle[0]` inclusive; the behavior then repeats `cycle` forever, stepping from its
/// last state back to `cycle[0]`. A one-state cycle is infinite stuttering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LassoIndices {
    pub prefix: Vec<usize>,
    pub cycle: Vec<usize>,
}

struct ConstraintTable {
    label: &'static str,
    strong: bool,
    enabled: Vec<bool>,
    taken: Vec<Vec<bool>>,
}

/// Enabledness and occurrence of every fairness constraint's `<<A>>_v` step,
/// evaluated once over the whole graph. `taken[s][e]` holds when the `e`-th edge out
/// of `s` is an `A` step that changes the subscript `v`, so `WF_x(A)` ignores
/// `A` steps that leave `x` unchanged and stuttering never counts as taking `A`.
/// A state enables `<<A>>_v` when one of its explored edges takes it, or when one of
/// its successors outside the `CONSTRAINT` (`excluded[s]`, never part of a behavior)
/// would: as in TLC, the constraint prunes behaviors, not enabledness. `taken` is
/// exact for every edge inside a full-graph SCC, the only edges a fair cycle can
/// use; edges that leave the SCC are evaluated only until one proves enabledness.
pub struct FairnessTable {
    constraints: Vec<ConstraintTable>,
}

enum Waypoint {
    Node(usize),
    Edge(usize, usize),
}

impl FairnessTable {
    pub fn build(
        graph: &StateGraph,
        fairness: &[FairnessConstraint],
        excluded: &[Vec<State>],
        vars: &[Arc<str>],
        constants: &Env,
        defs: &Definitions,
    ) -> Result<Self> {
        let mut constraints = Vec::with_capacity(fairness.len());
        let component_of = if fairness.is_empty() {
            Vec::new()
        } else {
            component_membership(graph)
        };
        for constraint in fairness {
            let (label, strong, subscript, action) = match constraint {
                FairnessConstraint::Weak(subscript, action) => ("WF", false, subscript, action),
                FairnessConstraint::Strong(subscript, action) => ("SF", true, subscript, action),
            };
            let mut bindings = Bindings::new(vars, constants, defs);
            let mut subscript_values = Vec::with_capacity(graph.state_count());
            for state in graph.states.iter() {
                bindings.bind(state);
                subscript_values.push(bindings.value(subscript)?);
            }
            let mut enabled = Vec::with_capacity(graph.state_count());
            let mut taken = Vec::with_capacity(graph.state_count());
            for (state_idx, state) in graph.states.iter().enumerate() {
                bindings.bind(state);
                let edges = graph.successors(state_idx);
                let mut row = vec![false; edges.len()];
                let occurs_at = |edge_idx: usize, bindings: &mut Bindings| -> Result<bool> {
                    let target = edges[edge_idx].target;
                    if target == state_idx
                        || subscript_values[target] == subscript_values[state_idx]
                    {
                        return Ok(false);
                    }
                    match graph.get_state(target) {
                        Some(next) => {
                            bindings.bind_next(next);
                            bindings.holds(action, "fairness action")
                        }
                        None => Ok(false),
                    }
                };
                let mut any = false;
                for (edge_idx, edge) in edges.iter().enumerate() {
                    if component_of[edge.target] == component_of[state_idx] {
                        row[edge_idx] = occurs_at(edge_idx, &mut bindings)?;
                        any |= row[edge_idx];
                    }
                }
                if !any {
                    for (edge_idx, edge) in edges.iter().enumerate() {
                        if component_of[edge.target] != component_of[state_idx]
                            && occurs_at(edge_idx, &mut bindings)?
                        {
                            row[edge_idx] = true;
                            any = true;
                            break;
                        }
                    }
                }
                if !any {
                    for next in excluded.get(state_idx).into_iter().flatten() {
                        bindings.bind(next);
                        let changes = bindings.value(subscript)? != subscript_values[state_idx];
                        bindings.bind(state);
                        bindings.bind_next(next);
                        if changes && bindings.holds(action, "fairness action")? {
                            any = true;
                            break;
                        }
                    }
                }
                enabled.push(any);
                taken.push(row);
            }
            constraints.push(ConstraintTable {
                label,
                strong,
                enabled,
                taken,
            });
        }
        Ok(Self { constraints })
    }

    fn enabled_at<G: LivenessGraph>(&self, constraint: usize, graph: &G, node: usize) -> bool {
        self.constraints[constraint].enabled[graph.state_of(node)]
    }

    fn taken_on<G: LivenessGraph>(
        &self,
        constraint: usize,
        graph: &G,
        node: usize,
        state_edge: usize,
    ) -> bool {
        self.constraints[constraint].taken[graph.state_of(node)][state_edge]
    }

    fn taken_within<G: LivenessGraph>(
        &self,
        constraint: usize,
        graph: &G,
        component: &[usize],
        members: &HashSet<usize>,
    ) -> Option<(usize, usize)> {
        component.iter().find_map(|&node| {
            graph
                .edges(node)
                .find(|&(target, state_edge)| {
                    members.contains(&target) && self.taken_on(constraint, graph, node, state_edge)
                })
                .map(|(target, _)| (node, target))
        })
    }

    /// Maximal fair strongly connected components inside `subset`, by Emerson–Lei
    /// refinement. A component that keeps `A` enabled in every state without ever
    /// taking it violates `WF(A)` on every cycle inside it and is discarded. A
    /// component that enables `A` somewhere but never takes it can still hold a
    /// cycle fair to `SF(A)` that avoids every `A`-enabled state, so those states are
    /// removed and the remainder is decomposed again.
    pub(crate) fn fair_components<G: LivenessGraph>(
        &self,
        graph: &G,
        subset: &HashSet<usize>,
    ) -> Vec<Vec<usize>> {
        let mut fair = Vec::new();
        let mut work = components(graph, subset);
        while let Some(component) = work.pop() {
            let members: HashSet<usize> = component.iter().copied().collect();
            let mut remove: HashSet<usize> = HashSet::new();
            let mut unfair = false;
            for (constraint, table) in self.constraints.iter().enumerate() {
                let enabled = |node: usize| self.enabled_at(constraint, graph, node);
                if !component.iter().any(|&n| enabled(n))
                    || self
                        .taken_within(constraint, graph, &component, &members)
                        .is_some()
                {
                    continue;
                }
                if table.strong {
                    remove.extend(component.iter().copied().filter(|&n| enabled(n)));
                } else if component.iter().all(|&n| enabled(n)) {
                    unfair = true;
                    break;
                }
            }
            if unfair {
                continue;
            }
            if remove.is_empty() {
                fair.push(component);
            } else {
                let rest: HashSet<usize> = members.difference(&remove).copied().collect();
                work.extend(components(graph, &rest));
            }
        }
        fair.sort();
        fair
    }

    /// A cycle through `component` that starts at its smallest state, passes every
    /// state in `must_visit`, and satisfies every fairness constraint: it visits a
    /// state where a weakly fair action is disabled, or takes an edge of that action,
    /// and takes an edge of every strongly fair action enabled inside the component.
    /// The entry state alone is a cycle only when it has a self-loop, which every
    /// state-graph state does but a product node need not; otherwise the cycle leaves
    /// through a successor inside the component and returns.
    pub(crate) fn witness_cycle<G: LivenessGraph>(
        &self,
        graph: &G,
        component: &[usize],
        must_visit: &[usize],
    ) -> Vec<usize> {
        let members: HashSet<usize> = component.iter().copied().collect();
        let entry = component[0];
        let mut waypoints: Vec<Waypoint> = must_visit.iter().map(|&s| Waypoint::Node(s)).collect();
        for (constraint, table) in self.constraints.iter().enumerate() {
            let enabled = |node: usize| self.enabled_at(constraint, graph, node);
            if !component.iter().any(|&n| enabled(n)) {
                continue;
            }
            let idle = if table.strong {
                None
            } else {
                component.iter().copied().find(|&n| !enabled(n))
            };
            match idle {
                Some(state_idx) => waypoints.push(Waypoint::Node(state_idx)),
                None => {
                    if let Some((from, to)) =
                        self.taken_within(constraint, graph, component, &members)
                    {
                        waypoints.push(Waypoint::Edge(from, to));
                    }
                }
            }
        }
        let mut cycle = vec![entry];
        let mut current = entry;
        for waypoint in waypoints {
            match waypoint {
                Waypoint::Node(target) => {
                    extend_path(graph, &members, &mut cycle, &mut current, target)
                }
                Waypoint::Edge(from, to) => {
                    extend_path(graph, &members, &mut cycle, &mut current, from);
                    cycle.push(to);
                    current = to;
                }
            }
        }
        let self_loop = graph.edges(entry).any(|(target, _)| target == entry);
        if cycle.len() == 1
            && !self_loop
            && let Some((step, _)) = graph
                .edges(entry)
                .find(|(target, _)| members.contains(target))
        {
            cycle.push(step);
            current = step;
        }
        extend_path(graph, &members, &mut cycle, &mut current, entry);
        if cycle.len() > 1 && cycle.last() == Some(&entry) {
            cycle.pop();
        }
        cycle
    }

    /// For each fairness constraint, whether its action is enabled somewhere on the
    /// reported cycle and whether the cycle takes it, with whether the cycle satisfies
    /// the constraint: `WF` unless the action is enabled at every state of the cycle
    /// and never taken, `SF` unless it is enabled somewhere and never taken.
    pub fn fairness_info<G: LivenessGraph>(
        &self,
        graph: &G,
        cycle: &[usize],
    ) -> Vec<(String, bool)> {
        self.constraints
            .iter()
            .enumerate()
            .map(|(constraint, table)| {
                let enabled = cycle.iter().any(|&n| self.enabled_at(constraint, graph, n));
                let continuously = cycle.iter().all(|&n| self.enabled_at(constraint, graph, n));
                let taken = cycle.iter().enumerate().any(|(i, &from)| {
                    let to = cycle[(i + 1) % cycle.len()];
                    graph.edges(from).any(|(target, state_edge)| {
                        target == to && self.taken_on(constraint, graph, from, state_edge)
                    })
                });
                (
                    format!(
                        "{}(action): enabled={}, taken={}",
                        table.label, enabled, taken
                    ),
                    taken || !if table.strong { enabled } else { continuously },
                )
            })
            .collect()
    }
}

/// Search for a fair behavior of the graph that violates `property`, whose shape is
/// one the property extraction produces: `LeadsTo(P, Q)`, `Eventually(Always(P))`
/// (`<>[]P`), `Eventually(P)` (`<>P`), or a bare state predicate `P` (`[]<>P`).
pub fn find_violation(
    graph: &StateGraph,
    table: &FairnessTable,
    property: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<LassoIndices>> {
    match property {
        Expr::LeadsTo(p, q) => leads_to(graph, table, p, q, vars, constants, defs),
        Expr::Eventually(inner) => match inner.as_ref() {
            Expr::Always(p) => stable_eventually(graph, table, p, vars, constants, defs),
            _ => eventually(graph, table, inner, vars, constants, defs),
        },
        _ => infinitely_often(graph, table, property, vars, constants, defs),
    }
}

/// `[]<>P` fails exactly when a reachable fair cycle stays in `~P` forever.
fn infinitely_often(
    graph: &StateGraph,
    table: &FairnessTable,
    p: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<LassoIndices>> {
    let holds = truth(graph, p, vars, constants, defs)?;
    let subset: HashSet<usize> = (0..holds.len()).filter(|&s| !holds[s]).collect();
    Ok(table
        .fair_components(graph, &subset)
        .into_iter()
        .next()
        .map(|component| {
            let cycle = table.witness_cycle(graph, &component, &[]);
            LassoIndices {
                prefix: parent_path(graph, cycle[0]),
                cycle,
            }
        }))
}

/// `<>[]P` fails exactly when a reachable fair cycle visits `~P` infinitely often.
fn stable_eventually(
    graph: &StateGraph,
    table: &FairnessTable,
    p: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<LassoIndices>> {
    let holds = truth(graph, p, vars, constants, defs)?;
    let all: HashSet<usize> = (0..holds.len()).collect();
    for component in table.fair_components(graph, &all) {
        if let Some(&not_p) = component.iter().find(|&&s| !holds[s]) {
            let cycle = table.witness_cycle(graph, &component, &[not_p]);
            return Ok(Some(LassoIndices {
                prefix: parent_path(graph, cycle[0]),
                cycle,
            }));
        }
    }
    Ok(None)
}

/// `<>P` fails exactly when a fair behavior never reaches `P`: its whole path,
/// starting from an initial state, stays in `~P`, including the cycle it ends in.
fn eventually(
    graph: &StateGraph,
    table: &FairnessTable,
    p: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<LassoIndices>> {
    let holds = truth(graph, p, vars, constants, defs)?;
    let allowed: Vec<bool> = holds.iter().map(|&h| !h).collect();
    let sources: Vec<usize> = (0..holds.len())
        .filter(|&s| allowed[s] && graph.parents.get(s).copied().flatten().is_none())
        .collect();
    let (reached, parent) = reach_within(graph, &sources, &allowed);
    let subset: HashSet<usize> = (0..reached.len()).filter(|&s| reached[s]).collect();
    Ok(table
        .fair_components(graph, &subset)
        .into_iter()
        .next()
        .map(|component| {
            let cycle = table.witness_cycle(graph, &component, &[]);
            LassoIndices {
                prefix: path_back(&parent, cycle[0]),
                cycle,
            }
        }))
}

/// `P ~> Q` fails exactly when some reachable `P /\ ~Q` state starts a fair
/// continuation that stays in `~Q` forever. The `P` state may lie anywhere before
/// the cycle, not only inside it.
fn leads_to(
    graph: &StateGraph,
    table: &FairnessTable,
    p: &Expr,
    q: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<LassoIndices>> {
    let p_holds = truth(graph, p, vars, constants, defs)?;
    let q_holds = truth(graph, q, vars, constants, defs)?;
    let allowed: Vec<bool> = q_holds.iter().map(|&h| !h).collect();
    let sources: Vec<usize> = (0..p_holds.len())
        .filter(|&s| p_holds[s] && !q_holds[s])
        .collect();
    let (reached, parent) = reach_within(graph, &sources, &allowed);
    let subset: HashSet<usize> = (0..reached.len()).filter(|&s| reached[s]).collect();
    Ok(table
        .fair_components(graph, &subset)
        .into_iter()
        .next()
        .map(|component| {
            let cycle = table.witness_cycle(graph, &component, &[]);
            let continuation = path_back(&parent, cycle[0]);
            let mut prefix = parent_path(graph, continuation[0]);
            prefix.extend(continuation.into_iter().skip(1));
            LassoIndices { prefix, cycle }
        }))
}

pub(crate) fn truth(
    graph: &StateGraph,
    expr: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Vec<bool>> {
    let mut bindings = Bindings::new(vars, constants, defs);
    graph
        .states
        .iter()
        .map(|state| {
            bindings.bind(state);
            bindings.holds(expr, "liveness property")
        })
        .collect()
}

/// One evaluation environment reused across a whole pass over the graph. Constants
/// are bound once; each state's variables, and for actions its successor's primed
/// variables, overwrite the previous state's before evaluating.
pub(crate) struct Bindings<'a> {
    env: Env,
    vars: &'a [Arc<str>],
    primed: Vec<Arc<str>>,
    defs: &'a Definitions,
}

impl<'a> Bindings<'a> {
    pub(crate) fn new(vars: &'a [Arc<str>], constants: &Env, defs: &'a Definitions) -> Self {
        Self {
            env: constants.clone(),
            vars,
            primed: vars
                .iter()
                .map(|var| crate::intern::primed_name(var))
                .collect(),
            defs,
        }
    }

    pub(crate) fn bind(&mut self, state: &State) {
        for (var, val) in self.vars.iter().zip(&state.values) {
            self.env.insert(var.clone(), val.clone());
        }
    }

    pub(crate) fn bind_next(&mut self, state: &State) {
        for (var, val) in self.primed.iter().zip(&state.values) {
            self.env.insert(var.clone(), val.clone());
        }
    }

    pub(crate) fn value(&mut self, expr: &Expr) -> Result<Value> {
        eval(expr, &mut self.env, self.defs)
    }

    pub(crate) fn holds(&mut self, expr: &Expr, context: &'static str) -> Result<bool> {
        match self.value(expr)? {
            Value::Bool(b) => Ok(b),
            got => Err(EvalError::TypeMismatch {
                expected: "Bool",
                got,
                context: Some(context),
                span: None,
            }),
        }
    }
}

/// The full-graph SCC of every state. A fair component is always a sub-component of
/// one of these, so an edge that leaves its state's SCC can decide enabledness but
/// can never be a step taken inside a fair cycle.
fn component_membership(graph: &StateGraph) -> Vec<usize> {
    let mut component_of = vec![0; graph.state_count()];
    for (id, scc) in crate::scc::compute_sccs(graph).into_iter().enumerate() {
        for state_idx in scc.states {
            component_of[state_idx] = id;
        }
    }
    component_of
}

fn components<G: LivenessGraph>(graph: &G, subset: &HashSet<usize>) -> Vec<Vec<usize>> {
    crate::scc::sccs_within(graph, subset)
        .into_iter()
        .filter(|scc| !scc.is_trivial)
        .map(|scc| {
            let mut states = scc.states;
            states.sort_unstable();
            states
        })
        .collect()
}

pub(crate) fn reach_within<G: LivenessGraph>(
    graph: &G,
    sources: &[usize],
    allowed: &[bool],
) -> (Vec<bool>, Vec<Option<usize>>) {
    let mut reached = vec![false; graph.node_count()];
    let mut parent = vec![None; graph.node_count()];
    let mut queue: VecDeque<usize> = VecDeque::new();
    for &source in sources {
        if allowed[source] && !reached[source] {
            reached[source] = true;
            queue.push_back(source);
        }
    }
    while let Some(node) = queue.pop_front() {
        for (target, _) in graph.edges(node) {
            if allowed[target] && !reached[target] {
                reached[target] = true;
                parent[target] = Some(node);
                queue.push_back(target);
            }
        }
    }
    (reached, parent)
}

pub(crate) fn path_back(parent: &[Option<usize>], target: usize) -> Vec<usize> {
    let mut path = vec![target];
    let mut current = target;
    while let Some(previous) = parent[current] {
        path.push(previous);
        current = previous;
    }
    path.reverse();
    path
}

fn parent_path(graph: &StateGraph, target: usize) -> Vec<usize> {
    path_back(&graph.parents, target)
}

fn extend_path<G: LivenessGraph>(
    graph: &G,
    members: &HashSet<usize>,
    cycle: &mut Vec<usize>,
    current: &mut usize,
    target: usize,
) {
    if *current == target {
        return;
    }
    let (reached, parent) = {
        let allowed: Vec<bool> = (0..graph.node_count())
            .map(|n| members.contains(&n))
            .collect();
        reach_within(graph, &[*current], &allowed)
    };
    debug_assert!(
        reached[target],
        "fair components are strongly connected, so every waypoint is reachable"
    );
    if !reached[target] {
        return;
    }
    cycle.extend(path_back(&parent, target).into_iter().skip(1));
    *current = target;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::State;
    use crate::graph::StateGraph;

    fn var(name: &str) -> Expr {
        Expr::Var(Arc::from(name))
    }

    fn prime(name: &str) -> Expr {
        Expr::Prime(Arc::from(name))
    }

    fn lit(n: i64) -> Expr {
        Expr::Lit(Value::Int(n))
    }

    fn eq(l: Expr, r: Expr) -> Expr {
        Expr::Eq(Box::new(l), Box::new(r))
    }

    fn and(l: Expr, r: Expr) -> Expr {
        Expr::And(Box::new(l), Box::new(r))
    }

    fn eventually(e: Expr) -> Expr {
        Expr::Eventually(Box::new(e))
    }

    fn state(values: &[i64]) -> State {
        State {
            values: values.iter().map(|&v| Value::Int(v)).collect(),
        }
    }

    /// States are added in order with the given BFS parents; every state gets the
    /// implicit stuttering self-loop the checker adds before liveness checking.
    fn graph(states: &[(&[i64], Option<usize>)], edges: &[(usize, usize)]) -> StateGraph {
        let mut graph = StateGraph::new();
        for (values, parent) in states {
            graph.add_state(state(values), *parent);
        }
        for &(from, to) in edges {
            graph.add_edge(from, to, Some("Step".into()));
        }
        for idx in 0..graph.state_count() {
            graph.add_edge(idx, idx, None);
        }
        graph
    }

    fn violation(
        graph: &StateGraph,
        fairness: &[FairnessConstraint],
        property: &Expr,
        vars: &[&str],
    ) -> Option<LassoIndices> {
        let vars: Vec<Arc<str>> = vars.iter().map(|&v| Arc::from(v)).collect();
        let constants = Env::new();
        let defs = Definitions::new();
        let table = FairnessTable::build(graph, fairness, &[], &vars, &constants, &defs).unwrap();
        find_violation(graph, &table, property, &vars, &constants, &defs).unwrap()
    }

    fn increment() -> Expr {
        eq(prime("x"), Expr::Add(Box::new(var("x")), Box::new(lit(1))))
    }

    #[test]
    fn stable_eventually_flags_cycle_touching_not_p() {
        let g = graph(&[(&[0], None), (&[1], Some(0))], &[(0, 1), (1, 0)]);
        let property = eventually(Expr::Always(Box::new(eq(var("x"), lit(1)))));
        assert!(
            violation(&g, &[], &property, &["x"]).is_some(),
            "the 0 <-> 1 cycle revisits x=0 forever, so <>[](x=1) is violated"
        );
    }

    #[test]
    fn stable_eventually_holds_when_every_state_satisfies_p() {
        let g = graph(&[(&[1], None)], &[]);
        let property = eventually(Expr::Always(Box::new(eq(var("x"), lit(1)))));
        assert_eq!(violation(&g, &[], &property, &["x"]), None);
    }

    #[test]
    fn leads_to_finds_a_p_state_before_the_fair_cycle() {
        let g = graph(&[(&[0], None), (&[1], Some(0))], &[(0, 1)]);
        let fairness = [FairnessConstraint::Weak(var("x"), increment())];
        let property = Expr::LeadsTo(
            Box::new(eq(var("x"), lit(0))),
            Box::new(eq(var("x"), lit(2))),
        );
        assert_eq!(
            violation(&g, &fairness, &property, &["x"]),
            Some(LassoIndices {
                prefix: vec![0, 1],
                cycle: vec![1],
            }),
            "x=0 holds only before the fair stutter at x=1, which never reaches x=2"
        );
    }

    #[test]
    fn eventually_is_satisfied_by_a_p_state_before_the_cycle() {
        let g = graph(
            &[(&[0], None), (&[1], Some(0)), (&[2], Some(1))],
            &[(0, 1), (1, 2)],
        );
        let fairness = [FairnessConstraint::Weak(var("x"), increment())];
        assert_eq!(
            violation(&g, &fairness, &eventually(eq(var("x"), lit(1))), &["x"]),
            None,
            "every fair behavior passes x=1 on its way to the x=2 stutter"
        );
        assert!(
            violation(&g, &fairness, &eq(var("x"), lit(1)), &["x"]).is_some(),
            "[]<>(x=1) is still violated by the final x=2 stutter"
        );
    }

    #[test]
    fn weak_fairness_only_counts_steps_that_change_the_subscript() {
        let g = graph(&[(&[0, 0], None), (&[0, 1], Some(0))], &[(0, 1)]);
        let set_y = and(
            eq(var("y"), lit(0)),
            and(eq(prime("y"), lit(1)), eq(prime("x"), var("x"))),
        );
        let property = eventually(eq(var("y"), lit(1)));
        let on_x = [FairnessConstraint::Weak(var("x"), set_y.clone())];
        assert!(
            violation(&g, &on_x, &property, &["x", "y"]).is_some(),
            "the step leaves x unchanged, so WF_x(A) never forces it and stuttering at y=0 is fair"
        );
        let on_both = [FairnessConstraint::Weak(
            Expr::TupleLit(vec![var("x"), var("y")]),
            set_y,
        )];
        assert_eq!(
            violation(&g, &on_both, &property, &["x", "y"]),
            None,
            "the step changes <<x, y>>, so WF_<<x,y>>(A) forbids stuttering at y=0"
        );
    }

    #[test]
    fn strong_fairness_keeps_a_fair_cycle_that_avoids_the_enabled_state() {
        let g = graph(
            &[
                (&[0], None),
                (&[1], Some(0)),
                (&[2], Some(0)),
                (&[5], Some(1)),
            ],
            &[(0, 1), (0, 2), (1, 0), (2, 0), (1, 3)],
        );
        let a = and(eq(var("x"), lit(1)), eq(prime("x"), lit(5)));
        let fairness = [FairnessConstraint::Strong(var("x"), a)];
        let found = violation(&g, &fairness, &eventually(eq(var("x"), lit(5))), &["x"])
            .expect("the cycle between x=0 and x=2 never enables A, so SF(A) allows it forever");
        assert!(
            !found.cycle.contains(&1),
            "the witness cycle must avoid x=1, where A is enabled but never taken: {found:?}"
        );
    }

    /// Two disjoint copies of a state graph: node `2 * s + copy` stands for state `s`,
    /// the shape of a product with a two-node tableau that never switches nodes.
    struct Copies<'a>(&'a StateGraph);

    impl LivenessGraph for Copies<'_> {
        fn node_count(&self) -> usize {
            2 * self.0.state_count()
        }

        fn edges(&self, node: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
            let copy = node % 2;
            self.0
                .edges(node / 2)
                .map(move |(target, state_edge)| (2 * target + copy, state_edge))
        }

        fn edge(&self, node: usize, index: usize) -> Option<(usize, usize)> {
            self.0
                .edge(node / 2, index)
                .map(|(target, state_edge)| (2 * target + node % 2, state_edge))
        }

        fn state_of(&self, node: usize) -> usize {
            node / 2
        }
    }

    #[test]
    fn fairness_on_a_product_graph_matches_its_state_graph() {
        let g = graph(
            &[
                (&[0], None),
                (&[1], Some(0)),
                (&[2], Some(0)),
                (&[5], Some(1)),
            ],
            &[(0, 1), (0, 2), (1, 0), (2, 0), (1, 3)],
        );
        let a = and(eq(var("x"), lit(1)), eq(prime("x"), lit(5)));
        let fairness = [FairnessConstraint::Strong(var("x"), a)];
        let vars = [Arc::from("x")];
        let (constants, defs) = (Env::new(), Definitions::new());
        let table = FairnessTable::build(&g, &fairness, &[], &vars, &constants, &defs).unwrap();
        let product = Copies(&g);

        let on_states = table.fair_components(&g, &(0..g.state_count()).collect());
        let on_product = table.fair_components(&product, &(0..product.node_count()).collect());
        let mut projected: Vec<Vec<usize>> = on_product
            .iter()
            .map(|component| {
                let mut states: Vec<usize> = component.iter().map(|&n| n / 2).collect();
                states.sort_unstable();
                states.dedup();
                states
            })
            .collect();
        projected.sort();
        let mut doubled: Vec<Vec<usize>> = on_states
            .iter()
            .flat_map(|c| [c.clone(), c.clone()])
            .collect();
        doubled.sort();
        assert_eq!(
            projected, doubled,
            "each copy has the state graph's fair components"
        );

        for component in &on_product {
            let cycle = table.witness_cycle(&product, component, &[]);
            let states: Vec<usize> = cycle.iter().map(|&n| n / 2).collect();
            assert!(
                !states.contains(&1),
                "an SF-fair cycle avoids x=1, where A is enabled but not taken: {states:?}"
            );
            assert_eq!(
                table.fairness_info(&product, &cycle),
                table.fairness_info(&g, &states)
            );
        }
    }
}
