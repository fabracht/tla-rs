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
        let primed: Arc<str> = format!("{}'", var).into();
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

pub fn check_eventually(
    graph: &StateGraph,
    scc: &SCC,
    property: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Option<Vec<usize>>> {
    if scc.is_trivial {
        return Ok(None);
    }

    let mut not_p_states: HashSet<usize> = HashSet::new();
    for &state_idx in &scc.states {
        let Some(state) = graph.get_state(state_idx) else {
            continue;
        };
        let mut env = crate::eval::state_to_env(state, vars);
        for (k, v) in constants {
            env.insert(k.clone(), v.clone());
        }
        match eval(property, &mut env, defs) {
            Ok(Value::Bool(true)) => continue,
            Ok(Value::Bool(false)) => {
                not_p_states.insert(state_idx);
            }
            Ok(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "Bool",
                    got: Value::Bool(false),
                    context: Some("liveness property"),
                    span: None,
                });
            }
            Err(e) => return Err(e),
        }
    }

    if not_p_states.is_empty() {
        return Ok(None);
    }

    let sub_sccs = crate::scc::compute_sccs_in_subset(graph, &not_p_states);
    for sub in sub_sccs {
        if !sub.is_trivial {
            return Ok(Some(sub.states));
        }
    }
    Ok(None)
}

pub fn check_leads_to(
    graph: &StateGraph,
    scc: &SCC,
    p: &Expr,
    q: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Option<Vec<usize>>> {
    if scc.is_trivial {
        return Ok(None);
    }

    let mut p_and_not_q_states: Vec<usize> = Vec::new();
    let mut not_q_states: HashSet<usize> = HashSet::new();

    for &state_idx in &scc.states {
        let Some(state) = graph.get_state(state_idx) else {
            continue;
        };
        let mut env = crate::eval::state_to_env(state, vars);
        for (k, v) in constants {
            env.insert(k.clone(), v.clone());
        }

        let p_holds = match eval(p, &mut env, defs) {
            Ok(Value::Bool(b)) => b,
            Ok(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "Bool",
                    got: Value::Bool(false),
                    context: Some("leads-to antecedent"),
                    span: None,
                });
            }
            Err(e) => return Err(e),
        };

        let q_holds = match eval(q, &mut env, defs) {
            Ok(Value::Bool(b)) => b,
            Ok(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "Bool",
                    got: Value::Bool(false),
                    context: Some("leads-to consequent"),
                    span: None,
                });
            }
            Err(e) => return Err(e),
        };

        if !q_holds {
            not_q_states.insert(state_idx);
            if p_holds {
                p_and_not_q_states.push(state_idx);
            }
        }
    }

    if p_and_not_q_states.is_empty() || not_q_states.is_empty() {
        return Ok(None);
    }

    let sub_sccs = crate::scc::compute_sccs_in_subset(graph, &not_q_states);
    let mut nontrivial_targets: HashSet<usize> = HashSet::new();
    let mut violating_scc: Option<Vec<usize>> = None;
    for sub in &sub_sccs {
        if !sub.is_trivial {
            for &s in &sub.states {
                nontrivial_targets.insert(s);
            }
            if violating_scc.is_none() {
                violating_scc = Some(sub.states.clone());
            }
        }
    }

    if nontrivial_targets.is_empty() {
        return Ok(None);
    }

    for &start in &p_and_not_q_states {
        if reaches_target_within_subset(graph, start, &nontrivial_targets, &not_q_states) {
            return Ok(violating_scc);
        }
    }

    Ok(None)
}

fn reaches_target_within_subset(
    graph: &StateGraph,
    start: usize,
    targets: &HashSet<usize>,
    allowed: &HashSet<usize>,
) -> bool {
    if !allowed.contains(&start) {
        return false;
    }
    if targets.contains(&start) {
        return true;
    }
    let mut visited: HashSet<usize> = HashSet::new();
    let mut queue: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
    visited.insert(start);
    queue.push_back(start);
    while let Some(node) = queue.pop_front() {
        for edge in graph.successors(node) {
            let next = edge.target;
            if !allowed.contains(&next) || !visited.insert(next) {
                continue;
            }
            if targets.contains(&next) {
                return true;
            }
            queue.push_back(next);
        }
    }
    false
}

pub fn find_violating_scc(
    graph: &StateGraph,
    sccs: &[SCC],
    fairness: &[FairnessConstraint],
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Option<usize>> {
    for (i, scc) in sccs.iter().enumerate() {
        if !scc.is_trivial && !check_fairness_in_scc(graph, scc, fairness, vars, constants, defs)? {
            return Ok(Some(i));
        }
    }
    Ok(None)
}

pub fn build_counterexample(
    graph: &StateGraph,
    scc: &SCC,
    fairness: &[FairnessConstraint],
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<LivenessViolation> {
    let first_scc_state = scc.states[0];
    let prefix = graph.reconstruct_trace(first_scc_state);

    let cycle: Vec<State> = scc
        .states
        .iter()
        .filter_map(|&idx| graph.get_state(idx).cloned())
        .collect();

    let mut fairness_info = Vec::new();
    for constraint in fairness {
        match constraint {
            FairnessConstraint::Weak(_, action) => {
                let enabled = scc_any_enabled(graph, scc, action, vars, constants, defs)?;
                let taken = scc_has_action_edge(graph, scc, action, vars, constants, defs)?;
                fairness_info.push((
                    format!("WF(action): enabled={}, taken={}", enabled, taken),
                    taken,
                ));
            }
            FairnessConstraint::Strong(_, action) => {
                let enabled = scc_any_enabled(graph, scc, action, vars, constants, defs)?;
                let taken = scc_has_action_edge(graph, scc, action, vars, constants, defs)?;
                fairness_info.push((
                    format!("SF(action): enabled={}, taken={}", enabled, taken),
                    taken,
                ));
            }
        }
    }

    Ok(LivenessViolation {
        prefix,
        cycle,
        property: "fairness violation".into(),
        fairness_info,
    })
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
