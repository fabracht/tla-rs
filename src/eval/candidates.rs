use super::Definitions;
use super::contains_prime_ref;
use super::core::eval;
use super::error::Result;
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::eval_set;
use crate::ast::{Env, Expr, Value};
use std::collections::BTreeSet;
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

pub(crate) fn infer_candidates(
    next: &Expr,
    env: &mut Env,
    var: &Arc<str>,
    defs: &Definitions,
) -> Result<Vec<Value>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut candidates = BTreeSet::new();
    collect_candidates(next, env, var, defs, &mut candidates)?;

    if candidates.is_empty()
        && let Some(current) = env.get(var)
    {
        candidates.insert(current.clone());
    }

    let result = candidates.into_iter().collect();

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.infer_candidates_time_ns += _start.elapsed().as_nanos();
        stats.infer_candidates_calls += 1;
    });

    Ok(result)
}

fn collect_candidates(
    expr: &Expr,
    env: &mut Env,
    var: &Arc<str>,
    defs: &Definitions,
    candidates: &mut BTreeSet<Value>,
) -> Result<()> {
    match expr {
        Expr::Eq(l, r) => {
            if let Expr::Prime(name) = l.as_ref()
                && name == var
                && let Ok(val) = eval(r, env, defs)
            {
                candidates.insert(val);
            }
            if let Expr::Prime(name) = r.as_ref()
                && name == var
                && let Ok(val) = eval(l, env, defs)
            {
                candidates.insert(val);
            }
        }

        Expr::In(elem, set) => {
            if let Expr::Prime(name) = elem.as_ref()
                && name == var
                && let Ok(s) = eval_set(set, env, defs)
            {
                for val in s {
                    candidates.insert(val);
                }
            }
        }

        Expr::And(l, r) | Expr::Or(l, r) | Expr::Implies(l, r) | Expr::Equiv(l, r) => {
            if contains_prime_ref(l, defs) {
                collect_candidates(l, env, var, defs, candidates)?;
            }
            if contains_prime_ref(r, defs) {
                collect_candidates(r, env, var, defs, candidates)?;
            }
        }

        Expr::Exists(bound, domain, body) | Expr::Forall(bound, domain, body) => {
            if contains_prime_ref(body, defs)
                && let Ok(dom) = eval_set(domain, env, defs)
            {
                let bound = bound.clone();
                let prev = env.get(&bound).cloned();
                for val in dom {
                    env.insert(bound.clone(), val);
                    collect_candidates(body, env, var, defs, candidates)?;
                }
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
            }
        }

        Expr::If(_, then_br, else_br) => {
            collect_candidates(then_br, env, var, defs, candidates)?;
            collect_candidates(else_br, env, var, defs, candidates)?;
        }

        Expr::Case(branches) => {
            for (_, result) in branches {
                collect_candidates(result, env, var, defs, candidates)?;
            }
        }

        Expr::Let(bound, binding, body) => {
            if let Ok(val) = eval(binding, env, defs) {
                let bound = bound.clone();
                let prev = env.insert(bound.clone(), val);
                collect_candidates(body, env, var, defs, candidates)?;
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
            }
        }

        Expr::Unchanged(vars) => {
            if vars.contains(var)
                && let Some(current) = env.get(var)
            {
                candidates.insert(current.clone());
            }
        }

        Expr::FnCall(name, args) => {
            if let Some((params, body)) = defs.get(name)
                && params.len() == args.len()
                && contains_prime_ref(body, defs)
            {
                let params: Vec<Arc<str>> = params.clone();
                let mut saved: Vec<(Arc<str>, Option<Value>)> = Vec::new();
                for (param, arg) in params.iter().zip(args.iter()) {
                    if let Ok(val) = eval(arg, env, defs) {
                        let prev = env.insert(param.clone(), val);
                        saved.push((param.clone(), prev));
                    }
                }
                collect_candidates(body, env, var, defs, candidates)?;
                for (param, prev) in saved {
                    match prev {
                        Some(v) => env.insert(param, v),
                        None => env.remove(&param),
                    };
                }
            }
        }

        Expr::LabeledAction(_, action) => {
            collect_candidates(action, env, var, defs, candidates)?;
        }

        _ => {}
    }
    Ok(())
}
