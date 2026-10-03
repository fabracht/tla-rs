//! Liveness checking against a tableau: the search for a fair behavior of the state
//! graph that satisfies a temporal formula (the negation of a property, conjoined
//! with the specification's temporal assumptions).
//!
//! The search runs on the product of the state graph with the formula's tableau. A
//! product node pairs a state with a tableau node whose state literals hold there;
//! a product edge follows a state-graph edge (the implicit stuttering self-loops
//! included) on which the tableau node's step literals hold, into a successor
//! tableau node consistent with the target state. A behavior satisfies the formula
//! exactly when it is the projection of an infinite product path from an initial
//! pair that eventually stays inside a strongly connected set of product nodes
//! fulfilling every eventuality. Fairness is checked on those sets by the same
//! Emerson–Lei refinement as for the state graph, through the product's projection
//! onto states and state-graph edges.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::ast::{Env, Expr};
use crate::eval::Definitions;
use crate::graph::{LivenessGraph, StateGraph};
use crate::liveness::{Bindings, FairnessTable, LassoIndices, Result, path_back, reach_within};
use crate::ltl::{Atom, AtomTable, Literal, Ltl};
use crate::tableau::{self, Tableau};

/// The product of the state graph and a tableau, restricted to the pairs reachable
/// from an initial state paired with an initial tableau node.
pub struct Product {
    state: Vec<usize>,
    tableau_node: Vec<usize>,
    edges: Vec<Vec<(usize, usize)>>,
    initial: Vec<usize>,
}

impl LivenessGraph for Product {
    fn node_count(&self) -> usize {
        self.state.len()
    }

    fn edges(&self, node: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.edges[node].iter().copied()
    }

    fn edge(&self, node: usize, index: usize) -> Option<(usize, usize)> {
        self.edges[node].get(index).copied()
    }

    fn state_of(&self, node: usize) -> usize {
        self.state[node]
    }
}

/// What atoms are evaluated against: the spec's variables, constants and definitions.
#[derive(Clone, Copy)]
pub struct Model<'a> {
    pub vars: &'a [Arc<str>],
    pub constants: &'a Env,
    pub defs: &'a Definitions,
}

/// The truth of every atom on the state graph: state atoms per state, step atoms
/// per state-graph edge.
struct AtomTruth {
    state: Vec<Option<Vec<bool>>>,
    step: Vec<Option<Vec<Vec<bool>>>>,
}

impl AtomTruth {
    fn evaluate(graph: &StateGraph, atoms: &AtomTable, model: &Model<'_>) -> Result<Self> {
        let Model {
            vars,
            constants,
            defs,
        } = *model;
        let mut state = Vec::with_capacity(atoms.atoms().len());
        let mut step = Vec::with_capacity(atoms.atoms().len());
        for atom in atoms.atoms() {
            match atom {
                Atom::State(expr) => {
                    state.push(Some(crate::liveness::truth(
                        graph, expr, vars, constants, defs,
                    )?));
                    step.push(None);
                }
                Atom::Step { action, subscript } => {
                    state.push(None);
                    step.push(Some(crate::eval::with_enabled_vars(vars, || {
                        step_truth(graph, action, subscript, vars, constants, defs)
                    })?));
                }
            }
        }
        Ok(Self { state, step })
    }

    fn holds_at(&self, literal: Literal, state: usize) -> bool {
        self.state[literal.atom]
            .as_ref()
            .is_none_or(|truth| truth[state] == literal.positive)
    }

    fn holds_on(&self, literal: Literal, state: usize, edge: usize) -> bool {
        self.step[literal.atom]
            .as_ref()
            .is_none_or(|truth| truth[state][edge] == literal.positive)
    }
}

/// `[A]_v` on every state-graph edge: an `A` step, or one that leaves `v` unchanged.
fn step_truth(
    graph: &StateGraph,
    action: &Expr,
    subscript: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Vec<Vec<bool>>> {
    let mut bindings = Bindings::new(vars, constants, defs);
    let mut subscripts = Vec::with_capacity(graph.state_count());
    for state in graph.states.iter() {
        bindings.bind(state);
        subscripts.push(bindings.value(subscript)?);
    }
    let mut truth = Vec::with_capacity(graph.state_count());
    for (from, state) in graph.states.iter().enumerate() {
        let mut row = Vec::with_capacity(graph.successors(from).len());
        for (index, edge) in graph.successors(from).iter().enumerate() {
            let unchanged = match &edge.renamed {
                None => subscripts[edge.target] == subscripts[from],
                Some(reached) => {
                    bindings.bind(reached);
                    bindings.value(subscript)? == subscripts[from]
                }
            };
            let holds = unchanged || {
                bindings.bind(state);
                match graph.step_target(from, index) {
                    Some(next) => {
                        bindings.bind_next(next);
                        bindings.holds(action, "temporal property step")?
                    }
                    None => false,
                }
            };
            row.push(holds);
        }
        truth.push(row);
    }
    Ok(truth)
}

/// The product of `graph` with `tableau`, built breadth-first from the initial
/// states. `out_of_time` is polled while it grows; `None` means it was stopped.
fn build_product(
    graph: &StateGraph,
    tableau: &Tableau,
    truth: &AtomTruth,
    out_of_time: &dyn Fn() -> bool,
) -> Option<Product> {
    let (state_literals, step_literals): (Vec<Vec<Literal>>, Vec<Vec<Literal>>) = tableau
        .nodes
        .iter()
        .map(|node| {
            node.literals
                .iter()
                .partition(|l| truth.state[l.atom].is_some())
        })
        .unzip();
    let consistent =
        |t: usize, state: usize| state_literals[t].iter().all(|&l| truth.holds_at(l, state));
    let mut product = Product {
        state: Vec::new(),
        tableau_node: Vec::new(),
        edges: Vec::new(),
        initial: Vec::new(),
    };
    let mut index: HashMap<(usize, usize), usize> = HashMap::new();
    let mut add = |product: &mut Product, state: usize, t: usize| -> (usize, bool) {
        if let Some(&node) = index.get(&(state, t)) {
            return (node, false);
        }
        let node = product.state.len();
        product.state.push(state);
        product.tableau_node.push(t);
        product.edges.push(Vec::new());
        index.insert((state, t), node);
        (node, true)
    };

    let mut queue = std::collections::VecDeque::new();
    for state in 0..graph.state_count() {
        if graph.parents.get(state).copied().flatten().is_some() {
            continue;
        }
        for &t in &tableau.initial {
            if consistent(t, state) {
                let (node, is_new) = add(&mut product, state, t);
                if is_new {
                    product.initial.push(node);
                    queue.push_back(node);
                }
            }
        }
    }
    let mut processed = 0usize;
    while let Some(node) = queue.pop_front() {
        processed += 1;
        if processed.is_multiple_of(4096) && out_of_time() {
            return None;
        }
        let (state, t) = (product.state[node], product.tableau_node[node]);
        let mut out = Vec::new();
        for (edge_index, edge) in graph.successors(state).iter().enumerate() {
            if !step_literals[t]
                .iter()
                .all(|&l| truth.holds_on(l, state, edge_index))
            {
                continue;
            }
            for &next in &tableau.nodes[t].successors {
                if !consistent(next, edge.target) {
                    continue;
                }
                let (target, is_new) = add(&mut product, edge.target, next);
                if is_new {
                    queue.push_back(target);
                }
                out.push((target, edge_index));
            }
        }
        product.edges[node] = out;
    }
    Some(product)
}

pub enum Search {
    Violation(LassoIndices, Vec<(String, bool)>),
    Clean,
    OutOfTime,
}

/// Past this many disjuncts, the top of a formula is searched as one disjunct.
const MAX_DISJUNCTS: usize = 64;

/// One disjunct of a formula, compiled for the search as TLC does: its conjuncts
/// `[]<>p` and `<>[]p` over a state formula `p` become conditions on the accepting
/// component (some state satisfies `p`; every state satisfies `p`) instead of
/// tableau formulas, so a conjunction of many of them, typical of fairness-like
/// assumptions, costs no tableau nodes. The rest is the tableau.
pub struct Disjunct {
    tableau: Tableau,
    recurring: Vec<Ltl>,
    persistent: Vec<Ltl>,
}

/// A formula compiled into the disjuncts searched one after another.
pub struct Compiled {
    disjuncts: Vec<Disjunct>,
}

/// Compile `formula`, failing when a disjunct's tableau exceeds the node cap.
pub fn compile(formula: &Ltl, atoms: &AtomTable) -> std::result::Result<Compiled, String> {
    let disjuncts = top_disjuncts(formula)
        .into_iter()
        .map(|conjuncts| {
            let mut recurring = Vec::new();
            let mut persistent = Vec::new();
            let mut rest = Vec::new();
            for conjunct in conjuncts {
                match &conjunct {
                    Ltl::Always(inner) => match inner.as_ref() {
                        Ltl::Eventually(p) if state_formula(p, atoms) => {
                            recurring.push((**p).clone())
                        }
                        _ => rest.push(conjunct),
                    },
                    Ltl::Eventually(inner) => match inner.as_ref() {
                        Ltl::Always(p) if state_formula(p, atoms) => persistent.push((**p).clone()),
                        _ => rest.push(conjunct),
                    },
                    _ => rest.push(conjunct),
                }
            }
            Ok(Disjunct {
                tableau: tableau::build(&Ltl::And(rest))?,
                recurring,
                persistent,
            })
        })
        .collect::<std::result::Result<Vec<_>, String>>()?;
    Ok(Compiled { disjuncts })
}

/// Whether `formula` is a state formula: literals of state atoms under `/\` and
/// `\/`, judged at a single state.
fn state_formula(formula: &Ltl, atoms: &AtomTable) -> bool {
    match formula {
        Ltl::True | Ltl::False => true,
        Ltl::Literal(literal) => matches!(atoms.atoms()[literal.atom], Atom::State(_)),
        Ltl::And(parts) | Ltl::Or(parts) => parts.iter().all(|p| state_formula(p, atoms)),
        Ltl::Always(_) | Ltl::Eventually(_) => false,
    }
}

fn state_holds(formula: &Ltl, truth: &AtomTruth, state: usize) -> bool {
    match formula {
        Ltl::True => true,
        Ltl::False => false,
        Ltl::Literal(literal) => truth.holds_at(*literal, state),
        Ltl::And(parts) => parts.iter().all(|p| state_holds(p, truth, state)),
        Ltl::Or(parts) => parts.iter().any(|p| state_holds(p, truth, state)),
        Ltl::Always(_) | Ltl::Eventually(_) => false,
    }
}

/// The top of `formula` as a disjunction of conjunctions, distributing `/\` over
/// `\/` above its temporal operators; one disjunct when that would exceed
/// [`MAX_DISJUNCTS`].
fn top_disjuncts(formula: &Ltl) -> Vec<Vec<Ltl>> {
    fn expand(formula: &Ltl) -> Option<Vec<Vec<Ltl>>> {
        match formula {
            Ltl::Or(parts) => {
                let mut out = Vec::new();
                for part in parts {
                    out.extend(expand(part)?);
                    if out.len() > MAX_DISJUNCTS {
                        return None;
                    }
                }
                Some(out)
            }
            Ltl::And(parts) => {
                let mut out: Vec<Vec<Ltl>> = vec![Vec::new()];
                for part in parts {
                    let options = expand(part)?;
                    let mut next = Vec::new();
                    for prefix in &out {
                        for option in &options {
                            let mut combined = prefix.clone();
                            combined.extend(option.iter().cloned());
                            next.push(combined);
                            if next.len() > MAX_DISJUNCTS {
                                return None;
                            }
                        }
                    }
                    out = next;
                }
                Some(out)
            }
            other => Some(vec![vec![other.clone()]]),
        }
    }
    expand(formula).unwrap_or_else(|| vec![vec![formula.clone()]])
}

/// A fair behavior of `graph` satisfying the compiled formula, as a lasso of state
/// indices with the fairness information of its cycle.
pub fn find_behavior(
    graph: &StateGraph,
    table: &FairnessTable,
    compiled: &Compiled,
    atoms: &AtomTable,
    model: &Model<'_>,
    out_of_time: &dyn Fn() -> bool,
) -> Result<Search> {
    let truth = AtomTruth::evaluate(graph, atoms, model)?;
    for disjunct in &compiled.disjuncts {
        let Some(product) = build_product(graph, &disjunct.tableau, &truth, out_of_time) else {
            return Ok(Search::OutOfTime);
        };
        if let Some(found) = accepting_lasso(&product, disjunct, &truth, table) {
            return Ok(found);
        }
    }
    Ok(Search::Clean)
}

fn accepting_lasso(
    product: &Product,
    disjunct: &Disjunct,
    truth: &AtomTruth,
    table: &FairnessTable,
) -> Option<Search> {
    let tableau = &disjunct.tableau;
    let allowed: HashSet<usize> = (0..product.node_count())
        .filter(|&n| {
            disjunct
                .persistent
                .iter()
                .all(|p| state_holds(p, truth, product.state[n]))
        })
        .collect();
    for component in table.fair_components(product, &allowed) {
        let eventualities = (0..tableau.eventualities).map(|k| {
            component
                .iter()
                .copied()
                .find(|&n| tableau.nodes[product.tableau_node[n]].fulfills[k])
        });
        let recurrences = disjunct.recurring.iter().map(|p| {
            component
                .iter()
                .copied()
                .find(|&n| state_holds(p, truth, product.state[n]))
        });
        let Some(must_visit) = eventualities
            .chain(recurrences)
            .collect::<Option<Vec<usize>>>()
        else {
            continue;
        };
        let cycle = table.witness_cycle(product, &component, &must_visit);
        let everywhere = vec![true; product.node_count()];
        let (_, parent) = reach_within(product, &product.initial, &everywhere);
        let prefix = path_back(&parent, cycle[0]);
        let fairness = table.fairness_info(product, &cycle);
        let project = |nodes: Vec<usize>| nodes.into_iter().map(|n| product.state[n]).collect();
        return Some(Search::Violation(
            LassoIndices {
                prefix: project(prefix),
                cycle: project(cycle),
            },
            fairness,
        ));
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::ast::{State, Value};
    use crate::eval::eval;

    fn x() -> Expr {
        Expr::Var(Arc::from("x"))
    }

    /// A state graph where every state is reachable from state 0 through a random
    /// spanning tree (its BFS parents), plus `edges` and a stutter self-loop on every
    /// state, as the checker builds it.
    fn graph(rng: &mut fastrand::Rng, states: usize, edges: &[(usize, usize)]) -> StateGraph {
        let parents: Vec<Option<usize>> = (0..states)
            .map(|i| (i > 0).then(|| rng.usize(0..i)))
            .collect();
        let mut graph = StateGraph::new();
        for (i, &parent) in parents.iter().enumerate() {
            graph.add_state(
                State {
                    values: vec![Value::Int(i as i64)],
                },
                parent,
            );
        }
        for (i, &parent) in parents.iter().enumerate() {
            if let Some(parent) = parent {
                graph.add_edge(parent, i, None);
            }
        }
        for &(from, to) in edges {
            graph.add_edge(from, to, None);
        }
        for i in 0..states {
            if !graph.successors(i).iter().any(|e| e.target == i) {
                graph.add_edge(i, i, None);
            }
        }
        graph
    }

    struct Fixture {
        atoms: AtomTable,
        vars: Vec<Arc<str>>,
        constants: Env,
        defs: Definitions,
    }

    impl Fixture {
        fn new(subsets: &[Vec<i64>]) -> Self {
            let mut atoms = AtomTable::new();
            for subset in subsets {
                let set = Expr::SetEnum(subset.iter().map(|&v| Expr::Lit(Value::Int(v))).collect());
                atoms.intern_for_test(Atom::State(Expr::In(Box::new(x()), Box::new(set))));
            }
            atoms.intern_for_test(Atom::Step {
                action: Expr::Gt(Box::new(Expr::Prime(Arc::from("x"))), Box::new(x())),
                subscript: x(),
            });
            Self {
                atoms,
                vars: vec![Arc::from("x")],
                constants: Env::new(),
                defs: Definitions::new(),
            }
        }

        fn model(&self) -> Model<'_> {
            Model {
                vars: &self.vars,
                constants: &self.constants,
                defs: &self.defs,
            }
        }

        fn literal(&self, literal: Literal, state: i64, next: i64) -> bool {
            let mut env = Env::new();
            env.insert(Arc::from("x"), Value::Int(state));
            env.insert(Arc::from("x'"), Value::Int(next));
            let value = match &self.atoms.atoms()[literal.atom] {
                Atom::State(expr) => eval(expr, &mut env, &self.defs),
                Atom::Step { action, .. } if state == next => Ok(Value::Bool(true)),
                Atom::Step { action, .. } => eval(action, &mut env, &self.defs),
            };
            matches!(value, Ok(Value::Bool(b)) if b == literal.positive)
        }

        /// The formula on the lasso `states`, which repeats from `loop_start` on.
        fn holds(&self, formula: &Ltl, states: &[usize], loop_start: usize, at: usize) -> bool {
            let succ = |i: usize| {
                if i + 1 == states.len() {
                    loop_start
                } else {
                    i + 1
                }
            };
            let suffix = at.min(loop_start)..states.len();
            match formula {
                Ltl::True => true,
                Ltl::False => false,
                Ltl::Literal(l) => self.literal(*l, states[at] as i64, states[succ(at)] as i64),
                Ltl::And(parts) => parts.iter().all(|p| self.holds(p, states, loop_start, at)),
                Ltl::Or(parts) => parts.iter().any(|p| self.holds(p, states, loop_start, at)),
                Ltl::Always(inner) => suffix
                    .into_iter()
                    .all(|j| self.holds(inner, states, loop_start, j)),
                Ltl::Eventually(inner) => suffix
                    .into_iter()
                    .any(|j| self.holds(inner, states, loop_start, j)),
            }
        }

        fn search(&self, graph: &StateGraph, formula: &Ltl) -> Option<LassoIndices> {
            let table =
                FairnessTable::build(graph, &[], &[], &self.vars, &self.constants, &self.defs)
                    .unwrap();
            let compiled = compile(formula, &self.atoms).unwrap();
            match find_behavior(
                graph,
                &table,
                &compiled,
                &self.atoms,
                &self.model(),
                &|| false,
            )
            .unwrap()
            {
                Search::Violation(lasso, _) => Some(lasso),
                Search::Clean => None,
                Search::OutOfTime => panic!("no deadline in tests"),
            }
        }
    }

    /// Whether some lasso of at most `max_len` states satisfies `formula`.
    fn some_short_lasso_satisfies(
        fixture: &Fixture,
        graph: &StateGraph,
        formula: &Ltl,
        max_len: usize,
    ) -> bool {
        let mut paths: Vec<Vec<usize>> = vec![vec![0]];
        while let Some(path) = paths.pop() {
            let last = *path.last().unwrap();
            for (j, &state) in path.iter().enumerate() {
                let closes = graph.successors(last).iter().any(|e| e.target == state);
                if closes && fixture.holds(formula, &path, j, 0) {
                    return true;
                }
            }
            if path.len() < max_len {
                for edge in graph.successors(last) {
                    let mut longer = path.clone();
                    longer.push(edge.target);
                    paths.push(longer);
                }
            }
        }
        false
    }

    fn random_formula(rng: &mut fastrand::Rng, atoms: usize, depth: usize) -> Ltl {
        if depth == 0 || rng.u8(0..4) == 0 {
            return Ltl::Literal(Literal {
                atom: rng.usize(0..atoms),
                positive: rng.bool(),
            });
        }
        let sub = |rng: &mut fastrand::Rng| random_formula(rng, atoms, depth - 1);
        match rng.u8(0..4) {
            0 => Ltl::And(vec![sub(rng), sub(rng)]),
            1 => Ltl::Or(vec![sub(rng), sub(rng)]),
            2 => Ltl::Always(Box::new(sub(rng))),
            _ => Ltl::Eventually(Box::new(sub(rng))),
        }
    }

    #[test]
    fn found_behaviors_are_real_lassos_and_short_witnesses_are_found() {
        let mut rng = fastrand::Rng::with_seed(0x9D0C);
        let mut witnessed = 0;
        let mut clean = 0;
        for trial in 0..2000 {
            let states = rng.usize(2..5);
            let edges: Vec<(usize, usize)> = (0..rng.usize(1..2 * states))
                .map(|_| (rng.usize(0..states), rng.usize(0..states)))
                .collect();
            let graph = graph(&mut rng, states, &edges);
            let subsets: Vec<Vec<i64>> = (0..2)
                .map(|_| {
                    (0..states as i64)
                        .filter(|_| rng.bool())
                        .collect::<BTreeSet<i64>>()
                        .into_iter()
                        .collect()
                })
                .collect();
            let fixture = Fixture::new(&subsets);
            let formula = random_formula(&mut rng, fixture.atoms.atoms().len(), 3);
            let found = fixture.search(&graph, &formula);
            if found.is_none() {
                clean += 1;
            }
            if let Some(lasso) = &found {
                let mut states_seq = lasso.prefix.clone();
                let loop_start = states_seq.len() - 1;
                states_seq.extend(lasso.cycle.iter().skip(1));
                for pair in states_seq.windows(2) {
                    assert!(
                        graph
                            .successors(pair[0])
                            .iter()
                            .any(|e| e.target == pair[1]),
                        "trial {trial}: {pair:?} is not an edge"
                    );
                }
                let last = *states_seq.last().unwrap();
                assert!(
                    graph
                        .successors(last)
                        .iter()
                        .any(|e| e.target == lasso.cycle[0]),
                    "trial {trial}: the cycle does not close"
                );
                assert_eq!(
                    states_seq[0], 0,
                    "trial {trial}: starts at the initial state"
                );
                assert!(
                    fixture.holds(&formula, &states_seq, loop_start, 0),
                    "trial {trial}: {formula:?} fails on the reported lasso {lasso:?}"
                );
            }
            if some_short_lasso_satisfies(&fixture, &graph, &formula, 6) {
                witnessed += 1;
                assert!(
                    found.is_some(),
                    "trial {trial}: a short lasso satisfies {formula:?} but none was found"
                );
            }
        }
        assert!(
            witnessed > 400 && clean > 400,
            "both outcomes must be exercised: {witnessed} witnessed, {clean} clean"
        );
    }

    #[test]
    fn negated_properties_agree_with_the_property_checker_under_fairness() {
        use crate::ast::FairnessConstraint;
        let mut rng = fastrand::Rng::with_seed(0xFA1E);
        let set = |values: &[i64]| {
            Expr::SetEnum(values.iter().map(|&v| Expr::Lit(Value::Int(v))).collect())
        };
        for trial in 0..1500 {
            let states = rng.usize(2..6);
            let edges: Vec<(usize, usize)> = (0..rng.usize(1..2 * states + 1))
                .map(|_| (rng.usize(0..states), rng.usize(0..states)))
                .collect();
            let graph = graph(&mut rng, states, &edges);
            let mut pick = || -> Vec<i64> { (0..states as i64).filter(|_| rng.bool()).collect() };
            let (p_values, q_values, target) = (pick(), pick(), rng.i64(0..states as i64));
            let p = Expr::In(Box::new(x()), Box::new(set(&p_values)));
            let q = Expr::In(Box::new(x()), Box::new(set(&q_values)));
            let step = Expr::Eq(
                Box::new(Expr::Prime(Arc::from("x"))),
                Box::new(Expr::Lit(Value::Int(target))),
            );
            let fairness = match rng.u8(0..3) {
                0 => vec![],
                1 => vec![FairnessConstraint::Weak(x(), step)],
                _ => vec![FairnessConstraint::Strong(x(), step)],
            };
            let fixture = Fixture::new(&[p_values.clone(), q_values.clone()]);
            let table = FairnessTable::build(
                &graph,
                &fairness,
                &[],
                &fixture.vars,
                &fixture.constants,
                &fixture.defs,
            )
            .unwrap();
            let lit = |atom: usize, positive: bool| Ltl::Literal(Literal { atom, positive });
            let always = |f: Ltl| Ltl::Always(Box::new(f));
            let eventually = |f: Ltl| Ltl::Eventually(Box::new(f));
            let (property, negation) = match rng.u8(0..4) {
                0 => (p.clone(), eventually(always(lit(0, false)))),
                1 => (Expr::Eventually(Box::new(p.clone())), always(lit(0, false))),
                2 => (
                    Expr::Eventually(Box::new(Expr::Always(Box::new(p.clone())))),
                    always(eventually(lit(0, false))),
                ),
                _ => (
                    Expr::LeadsTo(Box::new(p.clone()), Box::new(q.clone())),
                    eventually(Ltl::And(vec![lit(0, true), always(lit(1, false))])),
                ),
            };
            let legacy = crate::liveness::find_violation(
                &graph,
                &table,
                &property,
                &fixture.vars,
                &fixture.constants,
                &fixture.defs,
            )
            .unwrap()
            .is_some();
            let tableau = matches!(
                find_behavior(
                    &graph,
                    &table,
                    &compile(&negation, &fixture.atoms).unwrap(),
                    &fixture.atoms,
                    &fixture.model(),
                    &|| false
                )
                .unwrap(),
                Search::Violation(..)
            );
            assert_eq!(
                tableau, legacy,
                "trial {trial}: {property:?} with {fairness:?} on {edges:?}"
            );
        }
    }

    #[test]
    fn recurrences_and_persistences_stay_out_of_the_tableau() {
        let mut atoms = AtomTable::new();
        let literals: Vec<Ltl> = (0..12)
            .map(|v| {
                let atom = atoms.intern_for_test(Atom::State(Expr::Eq(
                    Box::new(x()),
                    Box::new(Expr::Lit(Value::Int(v))),
                )));
                Ltl::Literal(Literal {
                    atom,
                    positive: true,
                })
            })
            .collect();
        let many = Ltl::And(
            literals
                .iter()
                .map(|l| Ltl::Always(Box::new(Ltl::Eventually(Box::new(l.clone())))))
                .chain([Ltl::Eventually(Box::new(Ltl::Always(Box::new(
                    literals[0].clone(),
                ))))])
                .collect(),
        );
        let compiled = compile(&many, &atoms).expect("12 recurrences need no tableau nodes");
        assert_eq!(compiled.disjuncts.len(), 1);
        assert_eq!(compiled.disjuncts[0].recurring.len(), 12);
        assert_eq!(compiled.disjuncts[0].persistent.len(), 1);
        assert!(compiled.disjuncts[0].tableau.nodes.len() <= 2);
    }

    #[test]
    fn top_disjunction_is_searched_one_disjunct_at_a_time() {
        let mut atoms = AtomTable::new();
        let p = Ltl::Literal(Literal {
            atom: atoms.intern_for_test(Atom::State(x())),
            positive: true,
        });
        let formula = Ltl::And(vec![
            Ltl::Or(vec![
                Ltl::Always(Box::new(p.clone())),
                Ltl::Eventually(Box::new(p.clone())),
            ]),
            Ltl::Always(Box::new(Ltl::Eventually(Box::new(p)))),
        ]);
        assert_eq!(compile(&formula, &atoms).unwrap().disjuncts.len(), 2);
    }
}
