use std::collections::BTreeSet;
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

use super::Definitions;
use super::core::eval;
use super::error::Result;
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::eval_bool;
use crate::ast::{Env, Expr, State, Value};

pub fn init_states(
    init: &Expr,
    vars: &[Arc<str>],
    domains: &Env,
    defs: &Definitions,
) -> Result<Vec<State>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut results = Vec::new();
    let mut initial_env = domains.clone();
    enumerate_init(init, &mut initial_env, vars, 0, domains, defs, &mut results)?;

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.init_states_time_ns += _start.elapsed().as_nanos();
        stats.init_states_calls += 1;
    });

    Ok(results)
}

fn enumerate_init(
    init: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    var_idx: usize,
    domains: &Env,
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    if var_idx >= vars.len() {
        if eval_bool(init, env, defs)? {
            let values: Vec<Value> = vars
                .iter()
                .filter_map(|var| env.get(var).cloned())
                .collect();
            results.push(State { values });
        }
        return Ok(());
    }

    let var = &vars[var_idx];

    let candidates = match domains.get(var) {
        Some(Value::Set(s)) => s.iter().cloned().collect::<Vec<_>>(),
        _ => infer_init_candidates(init, env, var, defs)?,
    };

    let var = var.clone();
    for candidate in candidates {
        env.insert(var.clone(), candidate);
        enumerate_init(init, env, vars, var_idx + 1, domains, defs, results)?;
    }
    env.remove(&var);

    Ok(())
}

fn infer_init_candidates(
    init: &Expr,
    env: &mut Env,
    var: &Arc<str>,
    defs: &Definitions,
) -> Result<Vec<Value>> {
    let mut candidates = BTreeSet::new();

    fn collect(
        expr: &Expr,
        env: &mut Env,
        var: &Arc<str>,
        defs: &Definitions,
        candidates: &mut BTreeSet<Value>,
    ) -> Result<()> {
        match expr {
            Expr::Eq(l, r) => {
                if let Expr::Var(name) = l.as_ref()
                    && name == var
                    && let Ok(val) = eval(r, env, defs)
                {
                    candidates.insert(val);
                }
                if let Expr::Var(name) = r.as_ref()
                    && name == var
                    && let Ok(val) = eval(l, env, defs)
                {
                    candidates.insert(val);
                }
            }
            Expr::In(elem, set) => {
                if let Expr::Var(name) = elem.as_ref()
                    && name == var
                    && let Ok(Value::Set(s)) = eval(set, env, defs)
                {
                    for val in s {
                        candidates.insert(val);
                    }
                }
            }
            Expr::And(l, r) | Expr::Or(l, r) => {
                collect(l, env, var, defs, candidates)?;
                collect(r, env, var, defs, candidates)?;
            }
            _ => {}
        }
        Ok(())
    }

    collect(init, env, var, defs, &mut candidates)?;
    Ok(candidates.into_iter().collect())
}
