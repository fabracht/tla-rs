use super::Definitions;
use super::ast_utils::{
    collect_conjuncts, collect_disjuncts_with_labels, contains_prime_ref, format_expr_brief,
    infer_action_name,
};
use super::candidates::infer_candidates;
use super::error::Result;
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::helpers::{eval_bool, eval_set};
use super::state::env_to_next_state;
use crate::ast::{Env, Expr, GuardEval, Transition, Value};
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

pub(crate) fn extract_guards_for_action(
    next: &Expr,
    env: &mut Env,
    defs: &Definitions,
    action: Option<&Arc<str>>,
) -> Result<Vec<GuardEval>> {
    let disjuncts = collect_disjuncts_with_labels(next, defs);

    for (disjunct, label) in &disjuncts {
        let matches = match (action, label) {
            (Some(a), Some(l)) => a == l,
            (None, None) => true,
            _ => false,
        };

        if matches {
            return extract_guards_from_expr(disjunct, env, defs);
        }
    }

    extract_guards_from_expr(next, env, defs)
}

fn extract_guards_from_expr(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<Vec<GuardEval>> {
    let mut guards = Vec::new();
    let conjuncts = collect_conjuncts(expr);

    for conjunct in conjuncts {
        if !contains_prime_ref(conjunct, defs) {
            let expr_str = format_expr_brief(conjunct);
            let result = eval_bool(conjunct, env, defs).unwrap_or(false);

            guards.push(GuardEval {
                expression: expr_str,
                result,
                bindings: Vec::new(),
            });
        }
    }

    Ok(guards)
}

pub(crate) fn next_states_impl(
    next: &Expr,
    base_env: &mut Env,
    vars: &[Arc<str>],
    primed_vars: &[Arc<str>],
    defs: &Definitions,
) -> Result<Vec<Transition>> {
    let ctx = EnumCtx {
        vars,
        primed_vars,
        defs,
    };
    if let Expr::Or(_, _) = next {
        let disjuncts = collect_disjuncts_with_labels(next, defs);
        let mut all_results = indexmap::IndexSet::new();
        for (disjunct, action) in &disjuncts {
            if let Expr::Exists(_, _, _) = disjunct {
                let mut results = Vec::new();
                expand_and_enumerate(disjunct, base_env, &ctx, action.clone(), &mut results)?;
                for transition in results {
                    all_results.insert(transition);
                }
            } else {
                let mut results = Vec::new();
                enumerate_next(disjunct, base_env, &ctx, 0, action.clone(), &mut results)?;
                for transition in results {
                    all_results.insert(transition);
                }
            }
        }
        return Ok(all_results.into_iter().collect());
    }

    let action = infer_action_name(next, defs);
    let mut results = Vec::new();
    enumerate_next(next, base_env, &ctx, 0, action, &mut results)?;
    Ok(results)
}

fn expand_and_enumerate(
    expr: &Expr,
    env: &mut Env,
    ctx: &EnumCtx<'_>,
    action: Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    match expr {
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, ctx.defs)?;
            let var = var.clone();
            for val in dom {
                env.insert(var.clone(), val);
                expand_and_enumerate(body, env, ctx, action.clone(), results)?;
            }
            env.remove(&var);
            Ok(())
        }
        _ => enumerate_next(expr, env, ctx, 0, action, results),
    }
}

fn evaluate_guards(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<bool> {
    for conjunct in collect_conjuncts(expr) {
        if !contains_prime_ref(conjunct, defs) && !eval_bool(conjunct, env, defs)? {
            return Ok(false);
        }
    }
    Ok(true)
}

struct EnumCtx<'a> {
    vars: &'a [Arc<str>],
    primed_vars: &'a [Arc<str>],
    defs: &'a Definitions,
}

fn enumerate_next(
    next: &Expr,
    env: &mut Env,
    ctx: &EnumCtx<'_>,
    var_idx: usize,
    action: Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let result = if var_idx == 0 {
        enumerate_next_with_refinement(next, env, ctx, action, results)
    } else {
        enumerate_next_impl(next, env, ctx, var_idx, action, results)
    };

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.enumerate_next_time_ns += _start.elapsed().as_nanos();
        stats.enumerate_next_calls += 1;
    });

    result
}

fn enumerate_next_impl(
    next: &Expr,
    env: &mut Env,
    ctx: &EnumCtx<'_>,
    var_idx: usize,
    action: Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    if var_idx == 0 && !evaluate_guards(next, env, ctx.defs)? {
        return Ok(());
    }

    if var_idx >= ctx.vars.len() {
        if eval_bool(next, env, ctx.defs)? {
            results.push(Transition {
                state: env_to_next_state(env, ctx.vars, ctx.primed_vars),
                action: action.clone(),
            });
        }
        return Ok(());
    }

    let var = &ctx.vars[var_idx];
    let primed = &ctx.primed_vars[var_idx];

    let candidates = infer_candidates(next, env, var, ctx.defs)?;

    for candidate in candidates {
        env.insert(primed.clone(), candidate);
        enumerate_next_impl(next, env, ctx, var_idx + 1, action.clone(), results)?;
    }
    env.remove(primed);

    Ok(())
}

fn enumerate_next_with_refinement(
    next: &Expr,
    env: &mut Env,
    ctx: &EnumCtx<'_>,
    action: Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    if !evaluate_guards(next, env, ctx.defs)? {
        return Ok(());
    }

    let mut all_candidates: Vec<Vec<Value>> = Vec::with_capacity(ctx.vars.len());
    for var in ctx.vars {
        all_candidates.push(infer_candidates(next, env, var, ctx.defs)?);
    }

    for (i, primed) in ctx.primed_vars.iter().enumerate() {
        if let Some(first) = all_candidates[i].first() {
            env.insert(primed.clone(), first.clone());
        }
    }

    let mut changed = true;
    let mut iterations = 0;
    while changed && iterations < 3 {
        changed = false;
        iterations += 1;

        for (i, var) in ctx.vars.iter().enumerate() {
            let new_candidates = infer_candidates(next, env, var, ctx.defs)?;
            if new_candidates != all_candidates[i] {
                all_candidates[i] = new_candidates;
                changed = true;
                if let Some(first) = all_candidates[i].first() {
                    env.insert(ctx.primed_vars[i].clone(), first.clone());
                }
            }
        }
    }

    for primed in ctx.primed_vars {
        env.remove(primed);
    }

    enumerate_combinations(next, env, ctx, 0, &all_candidates, &action, results)
}

fn enumerate_combinations(
    next: &Expr,
    env: &mut Env,
    ctx: &EnumCtx<'_>,
    idx: usize,
    all_candidates: &[Vec<Value>],
    action: &Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    if idx >= ctx.vars.len() {
        if eval_bool(next, env, ctx.defs)? {
            results.push(Transition {
                state: env_to_next_state(env, ctx.vars, ctx.primed_vars),
                action: action.clone(),
            });
        }
        return Ok(());
    }

    let primed = &ctx.primed_vars[idx];
    for candidate in &all_candidates[idx] {
        env.insert(primed.clone(), candidate.clone());
        enumerate_combinations(next, env, ctx, idx + 1, all_candidates, action, results)?;
    }
    env.remove(primed);

    Ok(())
}
