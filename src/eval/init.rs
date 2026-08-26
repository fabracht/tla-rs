use std::collections::BTreeSet;
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

use super::Definitions;
use super::core::eval;
use super::error::{EvalError, Result};
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::eval_bool;
use crate::{
    ast::{Env, Expr, State, Value},
    eval::candidates::{bind_params, restore_env},
};

pub fn init_states(
    init: &Expr,
    vars: &[Arc<str>],
    domains: &Env,
    defs: &Definitions,
) -> Result<Vec<State>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut initial_env = domains.clone();
    if super::walk::walk_enabled() {
        return super::walk::walk_init(init, &mut initial_env, vars, defs);
    }
    let mut results = Vec::new();
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
    let mut not_enumerable: Option<String> = None;

    fn collect(
        expr: &Expr,
        env: &mut Env,
        var: &Arc<str>,
        defs: &Definitions,
        candidates: &mut BTreeSet<Value>,
        not_enumerable: &mut Option<String>,
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
                {
                    match eval(set, env, defs) {
                        Ok(Value::Set(s)) => {
                            for val in s.iter() {
                                candidates.insert(val.clone());
                            }
                        }
                        Ok(other) => {
                            not_enumerable.get_or_insert(format!(
                                "{} \\in <set>: expected Set, got {}",
                                name,
                                super::error::value_type_name(&other)
                            ));
                        }
                        Err(e) => {
                            not_enumerable.get_or_insert(format!(
                                "{} \\in <set>: {}",
                                name,
                                e.short_description()
                            ));
                        }
                    }
                }
            }
            Expr::And(l, r) | Expr::Or(l, r) => {
                collect(l, env, var, defs, candidates, not_enumerable)?;
                collect(r, env, var, defs, candidates, not_enumerable)?;
            }
            Expr::QualifiedCall(instance_expr, op, args) => {
                use super::global_state::{PARAMETERIZED_INSTANCES, RESOLVED_INSTANCES};

                match instance_expr.as_ref() {
                    Expr::Var(instance_name) => {
                        let mut err = Ok(());
                        RESOLVED_INSTANCES.with(|inst_ref| {
                            let instances = inst_ref.borrow();
                            if let Some(instance_defs) = instances.get(instance_name)
                                && let Some((params, body)) = instance_defs.get(op)
                                && params.len() == args.len()
                            {
                                let mut merged_defs = defs.clone();
                                for (name, def) in instance_defs {
                                    merged_defs.insert(name.clone(), def.clone());
                                }
                                let params: Vec<Arc<str>> = params.clone();
                                let saved = bind_params(&params, args, env, defs);
                                err = collect(
                                    body,
                                    env,
                                    var,
                                    &merged_defs,
                                    candidates,
                                    not_enumerable,
                                );
                                restore_env(env, saved);
                            }
                        });
                        err?;
                    }
                    Expr::FnCall(instance_name, instance_args) => {
                        let mut err = Ok(());
                        PARAMETERIZED_INSTANCES.with(|inst_ref| {
                            let instances = inst_ref.borrow();
                            if let Some(param_inst) = instances.get(instance_name)
                                && instance_args.len() == param_inst.params.len()
                            {
                                let instance_defs = super::resolve_parameterized_defs_symbolic(
                                    param_inst,
                                    instance_args.to_vec(),
                                );

                                if let Some((params, body)) = instance_defs.get(op)
                                    && params.len() == args.len()
                                {
                                    let mut merged_defs = defs.clone();
                                    for (name, def) in &instance_defs {
                                        merged_defs.insert(name.clone(), def.clone());
                                    }
                                    let params: Vec<Arc<str>> = params.clone();
                                    let body = body.clone();
                                    let saved = bind_params(&params, args, env, defs);
                                    err = collect(
                                        &body,
                                        env,
                                        var,
                                        &merged_defs,
                                        candidates,
                                        not_enumerable,
                                    );
                                    restore_env(env, saved);
                                }
                            }
                        });
                        err?;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        Ok(())
    }

    collect(init, env, var, defs, &mut candidates, &mut not_enumerable)?;
    if candidates.is_empty()
        && let Some(source) = not_enumerable
    {
        return Err(EvalError::not_enumerable(var.clone(), source));
    }
    Ok(candidates.into_iter().collect())
}
