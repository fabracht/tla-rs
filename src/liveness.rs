use std::collections::HashSet;
use std::sync::Arc;

use crate::ast::{Env, Expr, FairnessConstraint, State, Value};
use crate::eval::{Definitions, EvalError, eval, is_action_enabled};
use crate::graph::StateGraph;
use crate::scc::SCC;

pub type Result<T> = std::result::Result<T, EvalError>;

#[derive(Debug, Clone)]
pub struct LivenessViolation {
    pub prefix: Vec<State>,
    pub cycle: Vec<State>,
    pub property: String,
    pub fairness_info: Vec<(String, bool)>,
}

pub fn check_fairness_in_scc(
    graph: &StateGraph,
    scc: &SCC,
    fairness: &[FairnessConstraint],
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    if scc.is_trivial {
        return Ok(true);
    }

    for constraint in fairness {
        match constraint {
            FairnessConstraint::Weak(_vars_expr, action) => {
                let all_enabled = scc_all_enabled(graph, scc, action, vars, constants, defs)?;
                if all_enabled {
                    let action_taken =
                        scc_has_action_edge(graph, scc, action, vars, constants, defs)?;
                    if !action_taken {
                        return Ok(false);
                    }
                }
            }
            FairnessConstraint::Strong(_vars_expr, action) => {
                let any_enabled = scc_any_enabled(graph, scc, action, vars, constants, defs)?;
                if any_enabled {
                    let action_taken =
                        scc_has_action_edge(graph, scc, action, vars, constants, defs)?;
                    if !action_taken {
                        return Ok(false);
                    }
                }
            }
        }
    }

    Ok(true)
}

fn scc_all_enabled(
    graph: &StateGraph,
    scc: &SCC,
    action: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    for &state_idx in &scc.states {
        if let Some(state) = graph.get_state(state_idx)
            && !is_action_enabled(action, state, vars, constants, defs)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn scc_any_enabled(
    graph: &StateGraph,
    scc: &SCC,
    action: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    for &state_idx in &scc.states {
        if let Some(state) = graph.get_state(state_idx)
            && is_action_enabled(action, state, vars, constants, defs)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn scc_has_action_edge(
    graph: &StateGraph,
    scc: &SCC,
    action: &Expr,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let scc_states: HashSet<usize> = scc.states.iter().copied().collect();

    for &state_idx in &scc.states {
        let Some(state) = graph.get_state(state_idx) else {
            continue;
        };
        for edge in graph.successors(state_idx) {
            if scc_states.contains(&edge.target)
                && let Some(target_state) = graph.get_state(edge.target)
                && action_matches(action, state, target_state, vars, constants, defs)?
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn action_matches(
    action: &Expr,
    current: &State,
    next: &State,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let mut env = Env::new();
    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = current.values.get(i) {
            env.insert(var.clone(), val.clone());
        }
        let primed = crate::intern::primed_name(var);
        if let Some(val) = next.values.get(i) {
            env.insert(primed, val.clone());
        }
    }
    for (k, v) in constants {
        env.insert(k.clone(), v.clone());
    }

    match eval(action, &mut env, defs) {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(_) => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: Value::Bool(false),
            context: Some("fairness action"),
            span: None,
        }),
        Err(e) => Err(e),
    }
}

fn eval_bool_at(
    graph: &StateGraph,
    state_idx: usize,
    expr: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
    context: &'static str,
) -> Result<Option<bool>> {
    let Some(state) = graph.get_state(state_idx) else {
        return Ok(None);
    };
    let mut env = crate::eval::state_to_env(state, vars);
    for (k, v) in constants {
        env.insert(k.clone(), v.clone());
    }
    match eval(expr, &mut env, defs) {
        Ok(Value::Bool(b)) => Ok(Some(b)),
        Ok(_) => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: Value::Bool(false),
            context: Some(context),
            span: None,
        }),
        Err(e) => Err(e),
    }
}

pub fn check_eventually(
    graph: &StateGraph,
    scc: &SCC,
    property: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Vec<Vec<usize>>> {
    if scc.is_trivial {
        return Ok(Vec::new());
    }

    let mut not_p_states: HashSet<usize> = HashSet::new();
    for &state_idx in &scc.states {
        if eval_bool_at(
            graph,
            state_idx,
            property,
            constants,
            defs,
            vars,
            "liveness property",
        )? == Some(false)
        {
            not_p_states.insert(state_idx);
        }
    }

    if not_p_states.is_empty() {
        return Ok(Vec::new());
    }

    let sub_sccs = crate::scc::compute_sccs_in_subset(graph, &not_p_states);
    Ok(sub_sccs
        .into_iter()
        .filter(|sub| !sub.is_trivial)
        .map(|sub| sub.states)
        .collect())
}

pub fn check_stable_eventually(
    graph: &StateGraph,
    scc: &SCC,
    property: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Vec<Vec<usize>>> {
    if scc.is_trivial {
        return Ok(Vec::new());
    }

    for &state_idx in &scc.states {
        if eval_bool_at(
            graph,
            state_idx,
            property,
            constants,
            defs,
            vars,
            "liveness property",
        )? == Some(false)
        {
            return Ok(vec![scc.states.clone()]);
        }
    }

    Ok(Vec::new())
}

pub fn check_leads_to(
    graph: &StateGraph,
    scc: &SCC,
    p: &Expr,
    q: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Vec<Vec<usize>>> {
    if scc.is_trivial {
        return Ok(Vec::new());
    }

    let mut p_and_not_q_states: Vec<usize> = Vec::new();
    let mut not_q_states: HashSet<usize> = HashSet::new();

    for &state_idx in &scc.states {
        let Some(p_holds) = eval_bool_at(
            graph,
            state_idx,
            p,
            constants,
            defs,
            vars,
            "leads-to antecedent",
        )?
        else {
            continue;
        };
        let Some(q_holds) = eval_bool_at(
            graph,
            state_idx,
            q,
            constants,
            defs,
            vars,
            "leads-to consequent",
        )?
        else {
            continue;
        };

        if !q_holds {
            not_q_states.insert(state_idx);
            if p_holds {
                p_and_not_q_states.push(state_idx);
            }
        }
    }

    if p_and_not_q_states.is_empty() || not_q_states.is_empty() {
        return Ok(Vec::new());
    }

    let sub_sccs = crate::scc::compute_sccs_in_subset(graph, &not_q_states);
    let nontrivial_sccs: Vec<Vec<usize>> = sub_sccs
        .into_iter()
        .filter(|sub| !sub.is_trivial)
        .map(|sub| sub.states)
        .collect();

    if nontrivial_sccs.is_empty() {
        return Ok(Vec::new());
    }

    let mut reachable: HashSet<usize> = HashSet::new();
    let mut queue: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
    for &start in &p_and_not_q_states {
        if not_q_states.contains(&start) && reachable.insert(start) {
            queue.push_back(start);
        }
    }
    while let Some(node) = queue.pop_front() {
        for edge in graph.successors(node) {
            if not_q_states.contains(&edge.target) && reachable.insert(edge.target) {
                queue.push_back(edge.target);
            }
        }
    }

    Ok(nontrivial_sccs
        .into_iter()
        .filter(|states| states.iter().any(|s| reachable.contains(s)))
        .collect())
}

pub fn fairness_info_for_scc(
    graph: &StateGraph,
    scc: &SCC,
    fairness: &[FairnessConstraint],
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Vec<(String, bool)>> {
    let mut fairness_info = Vec::new();
    for constraint in fairness {
        let (label, action) = match constraint {
            FairnessConstraint::Weak(_, action) => ("WF", action),
            FairnessConstraint::Strong(_, action) => ("SF", action),
        };
        let enabled = scc_any_enabled(graph, scc, action, vars, constants, defs)?;
        let taken = scc_has_action_edge(graph, scc, action, vars, constants, defs)?;
        fairness_info.push((
            format!("{}(action): enabled={}, taken={}", label, enabled, taken),
            taken,
        ));
    }
    Ok(fairness_info)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::State;
    use crate::graph::StateGraph;
    use crate::scc::compute_sccs;

    fn state_with_x(n: i64) -> State {
        State {
            values: vec![Value::Int(n)],
        }
    }

    fn eq_x(n: i64) -> Expr {
        Expr::Eq(
            Box::new(Expr::Var(Arc::from("x"))),
            Box::new(Expr::Lit(Value::Int(n))),
        )
    }

    #[test]
    fn stable_eventually_flags_cycle_touching_not_p() {
        let mut graph = StateGraph::new();
        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_edge(0, 1, Some("Toggle".into()));
        graph.add_edge(1, 0, Some("Toggle".into()));

        let sccs = compute_sccs(&graph);
        let scc = &sccs[0];
        assert!(!scc.is_trivial);

        let vars = vec![Arc::from("x")];
        let constants = Env::new();
        let defs = Definitions::new();

        let cycles =
            check_stable_eventually(&graph, scc, &eq_x(1), &constants, &defs, &vars).unwrap();
        assert_eq!(
            cycles.len(),
            1,
            "the cycle revisits x=0 (not-P) forever, so <>[](x=1) is violated"
        );
    }

    #[test]
    fn stable_eventually_ok_when_all_states_satisfy_p() {
        let mut graph = StateGraph::new();
        graph.add_state(state_with_x(1), None);
        graph.add_edge(0, 0, Some("Stay".into()));

        let sccs = compute_sccs(&graph);
        let scc = &sccs[0];
        assert!(!scc.is_trivial);

        let vars = vec![Arc::from("x")];
        let constants = Env::new();
        let defs = Definitions::new();

        let cycles =
            check_stable_eventually(&graph, scc, &eq_x(1), &constants, &defs, &vars).unwrap();
        assert!(
            cycles.is_empty(),
            "every state in the cycle satisfies x=1, so <>[](x=1) holds"
        );
    }

    #[test]
    fn fair_cycle_with_action() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));

        graph.add_edge(0, 1, Some("Inc".into()));
        graph.add_edge(1, 0, Some("Dec".into()));

        let sccs = compute_sccs(&graph);
        let scc = &sccs[0];

        let vars = vec![Arc::from("x")];
        let constants = Env::new();
        let defs = Definitions::new();

        let action = Expr::Lit(Value::Bool(true));
        let fairness = vec![FairnessConstraint::Weak(Expr::Var(Arc::from("x")), action)];

        let result = check_fairness_in_scc(&graph, scc, &fairness, &vars, &constants, &defs);
        assert!(result.is_ok());
        assert!(result.unwrap());
    }
}
