use super::Definitions;
use super::candidates::infer_candidates;
use super::enumerate::{extract_guards_for_action, next_states_impl};
use super::error::{EvalError, Result};
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::eval_bool;
use crate::ast::{Env, Expr, State, Transition, TransitionWithGuards};
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

pub fn make_primed_names(vars: &[Arc<str>]) -> Vec<Arc<str>> {
    vars.iter().map(|v| crate::intern::primed_name(v)).collect()
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

    let result = super::global_state::with_state_vars(vars, || {
        next_states_impl(next, env, vars, primed_vars, defs)
    });

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

    let result = super::global_state::with_state_vars(vars, || {
        next_states_with_guards_impl(next, env, vars, primed_vars, defs)
    });

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
        for (primed, val) in primed_vars.iter().zip(&transition.state.values) {
            base_env.insert(primed.clone(), val.clone());
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

/// The environment `ENABLED` evaluates its action in: the identifiers in `scope`
/// (constants, and the bound variables and operator parameters around `ENABLED`),
/// the variables of `current`, and no primed variable, since `ENABLED` binds them.
fn enabled_env(current: &State, vars: &[Arc<str>], scope: &Env) -> (Env, Vec<Arc<str>>) {
    let primed_vars = make_primed_names(vars);
    let mut env = scope.clone();
    for (var, primed) in vars.iter().zip(&primed_vars) {
        env.remove(primed);
        env.remove(var);
    }
    for (var, val) in vars.iter().zip(&current.values) {
        env.insert(var.clone(), val.clone());
    }
    (env, primed_vars)
}

/// `ENABLED <<A>>_v` in `current`: does some `A` step from it change `v`? As in TLC,
/// `v` is evaluated on each successor `A` produces, which may leave a variable
/// unassigned only if `v` does not depend on it. `scope` holds the identifiers in
/// scope, as for [`is_action_enabled`].
pub fn is_angle_action_enabled(
    action: &Expr,
    subscript: &Expr,
    current: &State,
    vars: &[Arc<str>],
    scope: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let (mut env, primed_vars) = enabled_env(current, vars, scope);
    angle_action_enabled_in(
        action,
        subscript,
        current,
        vars,
        &primed_vars,
        &mut env,
        defs,
    )
}

/// [`is_angle_action_enabled`] in an environment the caller prepared: it binds the
/// variables of `current` and the identifiers in scope, and no primed variable. On
/// return the variables may be bound to a successor's values instead.
pub(crate) fn angle_action_enabled_in(
    action: &Expr,
    subscript: &Expr,
    current: &State,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    env: &mut Env,
    defs: &Definitions,
) -> Result<bool> {
    let successors: Vec<(State, Vec<usize>)> = if super::walk::walk_enabled() {
        super::walk::walk_action_successors(action, env, vars, primed_vars, defs)?
    } else {
        next_states(action, current, vars, primed_vars, env, defs)?
            .into_iter()
            .map(|transition| (transition.state, Vec::new()))
            .collect()
    };
    let before = super::eval(subscript, env, defs)?;
    for (successor, unassigned) in &successors {
        for (index, (var, val)) in vars.iter().zip(&successor.values).enumerate() {
            if unassigned.contains(&index) {
                env.remove(var);
            } else {
                env.insert(var.clone(), val.clone());
            }
        }
        let after = super::eval(subscript, env, defs).map_err(|error| {
            if unassigned.is_empty() {
                return error;
            }
            let names: Vec<&str> = unassigned.iter().map(|&i| vars[i].as_ref()).collect();
            EvalError::domain_error(format!(
                "the action of ENABLED <<A>>_v (or of WF_v(A) / SF_v(A)) leaves {} unassigned, \
                 but the subscript v depends on it: {error}",
                names.join(", ")
            ))
        })?;
        if after != before {
            return Ok(true);
        }
    }
    Ok(false)
}

/// `ENABLED A` in `current`: does `A` have a successor from it? `scope` holds the
/// identifiers in scope: the constants, and the bound variables and operator
/// parameters `A` may refer to.
pub fn is_action_enabled(
    action: &Expr,
    current: &State,
    vars: &[Arc<str>],
    scope: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let (mut base_env, primed_vars) = enabled_env(current, vars, scope);
    if super::walk::walk_enabled() {
        return super::walk::walk_action_enabled(action, &mut base_env, vars, &primed_vars, defs);
    }
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
