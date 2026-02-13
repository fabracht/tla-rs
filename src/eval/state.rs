use super::Definitions;
use super::candidates::infer_candidates;
use super::enumerate::{extract_guards_for_action, next_states_impl};
use super::error::Result;
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::eval_bool;
use crate::ast::{Env, Expr, State, Transition, TransitionWithGuards};
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

pub fn make_primed_names(vars: &[Arc<str>]) -> Vec<Arc<str>> {
    vars.iter().map(|v| Arc::from(format!("{}'", v))).collect()
}

pub fn next_states(
    next: &Expr,
    current: &State,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    env: &mut Env,
    defs: &Definitions,
) -> Result<Vec<Transition>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = current.values.get(i) {
            env.insert(var.clone(), val.clone());
        }
    }

    let result = next_states_impl(next, env, vars, primed_vars, defs);

    for var in vars {
        env.remove(var);
    }

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.next_states_time_ns += _start.elapsed().as_nanos();
        stats.next_states_calls += 1;
    });

    result
}

pub fn next_states_with_guards(
    next: &Expr,
    current: &State,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    env: &mut Env,
    defs: &Definitions,
) -> Result<Vec<TransitionWithGuards>> {
    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = current.values.get(i) {
            env.insert(var.clone(), val.clone());
        }
    }

    let result = next_states_with_guards_impl(next, env, vars, primed_vars, defs);

    for var in vars {
        env.remove(var);
    }

    result
}

fn next_states_with_guards_impl(
    next: &Expr,
    base_env: &mut Env,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    defs: &Definitions,
) -> Result<Vec<TransitionWithGuards>> {
    let transitions = next_states_impl(next, base_env, vars, primed_vars, defs)?;

    let mut results = Vec::new();
    for transition in transitions {
        for (i, _var) in vars.iter().enumerate() {
            if let Some(val) = transition.state.values.get(i) {
                base_env.insert(primed_vars[i].clone(), val.clone());
            }
        }

        let guards = extract_guards_for_action(next, base_env, defs, transition.action.as_ref())?;

        for primed in primed_vars {
            base_env.remove(primed);
        }

        results.push(TransitionWithGuards {
            transition,
            guards,
            parameter_bindings: Vec::new(),
        });
    }

    Ok(results)
}

pub fn is_action_enabled(
    action: &Expr,
    current: &State,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let mut base_env = state_to_env(current, vars);
    for (k, v) in constants {
        base_env.insert(k.clone(), v.clone());
    }
    let primed_vars = make_primed_names(vars);
    check_enabled(action, &mut base_env, vars, &primed_vars, 0, defs)
}

fn check_enabled(
    action: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    var_idx: usize,
    defs: &Definitions,
) -> Result<bool> {
    if var_idx >= vars.len() {
        return eval_bool(action, env, defs);
    }

    let var = &vars[var_idx];
    let primed = &primed_vars[var_idx];
    let candidates = infer_candidates(action, env, var, defs)?;

    for candidate in candidates {
        env.insert(primed.clone(), candidate);
        if check_enabled(action, env, vars, primed_vars, var_idx + 1, defs)? {
            env.remove(primed);
            return Ok(true);
        }
    }
    env.remove(primed);

    Ok(false)
}

pub fn state_to_env(state: &State, vars: &[Arc<str>]) -> Env {
    vars.iter()
        .zip(state.values.iter())
        .map(|(var, val)| (var.clone(), val.clone()))
        .collect()
}

pub(crate) fn env_to_next_state(env: &Env, vars: &[Arc<str>], primed_vars: &[Arc<str>]) -> State {
    let mut values = Vec::with_capacity(vars.len());
    for primed in primed_vars {
        if let Some(val) = env.get(primed) {
            values.push(val.clone());
        }
    }
    State { values }
}
