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

fn extract_indexed_prime(expr: &Expr) -> Option<(Arc<str>, Vec<Expr>)> {
    match expr {
        Expr::Prime(name) => Some((name.clone(), vec![])),
        Expr::FnApp(f, idx) => {
            let (name, mut path) = extract_indexed_prime(f)?;
            path.push(idx.as_ref().clone());
            Some((name, path))
        }
        Expr::RecordAccess(r, field) => {
            let (name, mut path) = extract_indexed_prime(r)?;
            path.push(Expr::Lit(Value::Str(field.clone())));
            Some((name, path))
        }
        Expr::TupleAccess(t, idx) => {
            let (name, mut path) = extract_indexed_prime(t)?;
            path.push(Expr::Lit(Value::Int(*idx as i64)));
            Some((name, path))
        }
        _ => None,
    }
}

fn try_indexed_prime_candidate(
    prime_side: &Expr,
    value_side: &Expr,
    var: &Arc<str>,
    env: &mut Env,
    defs: &Definitions,
    candidates: &mut BTreeSet<Value>,
) {
    if let Some((name, path)) = extract_indexed_prime(prime_side)
        && !path.is_empty()
        && &name == var
    {
        let key_vals: Option<Vec<Value>> = path.iter().map(|p| eval(p, env, defs).ok()).collect();
        if let Some(keys) = key_vals
            && let Ok(new_val) = eval(value_side, env, defs)
            && let Some(current) = env.get(var)
            && let Some(updated) = apply_update(current, &keys, new_val)
        {
            candidates.insert(updated);
        }
    }
}

fn apply_update(base: &Value, keys: &[Value], new_val: Value) -> Option<Value> {
    if keys.is_empty() {
        return Some(new_val);
    }
    match base {
        Value::Fn(f) => {
            let key = &keys[0];
            if keys.len() == 1 {
                let mut new_f = f.clone();
                new_f.insert(key.clone(), new_val);
                Some(Value::Fn(new_f))
            } else {
                let inner = f.get(key)?;
                let updated_inner = apply_update(inner, &keys[1..], new_val)?;
                let mut new_f = f.clone();
                new_f.insert(key.clone(), updated_inner);
                Some(Value::Fn(new_f))
            }
        }
        Value::Record(rec) => {
            if let Value::Str(field) = &keys[0] {
                if keys.len() == 1 {
                    let mut new_rec = rec.clone();
                    new_rec.insert(field.clone(), new_val);
                    Some(Value::Record(new_rec))
                } else {
                    let inner = rec.get(field)?;
                    let updated_inner = apply_update(inner, &keys[1..], new_val)?;
                    let mut new_rec = rec.clone();
                    new_rec.insert(field.clone(), updated_inner);
                    Some(Value::Record(new_rec))
                }
            } else {
                None
            }
        }
        Value::Tuple(tup) => {
            if let Value::Int(idx) = &keys[0] {
                let idx = *idx as usize;
                if idx == 0 || idx > tup.len() {
                    return None;
                }
                if keys.len() == 1 {
                    let mut new_tup = tup.clone();
                    new_tup[idx - 1] = new_val;
                    Some(Value::Tuple(new_tup))
                } else {
                    let inner = tup.get(idx - 1)?;
                    let updated_inner = apply_update(inner, &keys[1..], new_val)?;
                    let mut new_tup = tup.clone();
                    new_tup[idx - 1] = updated_inner;
                    Some(Value::Tuple(new_tup))
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

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
            try_indexed_prime_candidate(l, r, var, env, defs, candidates);
            try_indexed_prime_candidate(r, l, var, env, defs, candidates);
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
            let expanded = super::core::expand_unchanged_vars(vars, defs);
            if expanded.contains(var)
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

        Expr::QualifiedCall(instance_expr, op, args) => {
            use super::global_state::{PARAMETERIZED_INSTANCES, RESOLVED_INSTANCES};

            match instance_expr.as_ref() {
                Expr::Var(instance_name) => {
                    RESOLVED_INSTANCES.with(|inst_ref| {
                        let instances = inst_ref.borrow();
                        if let Some(instance_defs) = instances.get(instance_name)
                            && let Some((params, body)) = instance_defs.get(op)
                            && params.len() == args.len()
                            && contains_prime_ref(body, defs)
                        {
                            let mut merged_defs = defs.clone();
                            for (name, def) in instance_defs {
                                merged_defs.insert(name.clone(), def.clone());
                            }
                            let params: Vec<Arc<str>> = params.clone();
                            let mut saved: Vec<(Arc<str>, Option<Value>)> = Vec::new();
                            for (param, arg) in params.iter().zip(args.iter()) {
                                if let Ok(val) = eval(arg, env, defs) {
                                    let prev = env.insert(param.clone(), val);
                                    saved.push((param.clone(), prev));
                                }
                            }
                            let _ = collect_candidates(body, env, var, &merged_defs, candidates);
                            for (param, prev) in saved {
                                match prev {
                                    Some(v) => {
                                        env.insert(param, v);
                                    }
                                    None => {
                                        env.remove(&param);
                                    }
                                };
                            }
                        }
                    });
                }
                Expr::FnCall(instance_name, instance_args) => {
                    PARAMETERIZED_INSTANCES.with(|inst_ref| {
                        let instances = inst_ref.borrow();
                        if let Some(param_inst) = instances.get(instance_name)
                            && instance_args.len() == param_inst.params.len()
                        {
                            let inst_arg_vals: Option<Vec<Value>> = instance_args
                                .iter()
                                .map(|arg| eval(arg, env, defs).ok())
                                .collect();

                            if let Some(inst_arg_vals) = inst_arg_vals {
                                let instance_defs =
                                    super::resolve_parameterized_defs(param_inst, inst_arg_vals);

                                if let Some((params, body)) = instance_defs.get(op)
                                    && params.len() == args.len()
                                {
                                    let mut merged_defs = defs.clone();
                                    for (name, def) in &instance_defs {
                                        merged_defs.insert(name.clone(), def.clone());
                                    }
                                    let params: Vec<Arc<str>> = params.clone();
                                    let body = body.clone();
                                    let mut saved: Vec<(Arc<str>, Option<Value>)> = Vec::new();
                                    for (param, arg) in params.iter().zip(args.iter()) {
                                        if let Ok(val) = eval(arg, env, defs) {
                                            let prev = env.insert(param.clone(), val);
                                            saved.push((param.clone(), prev));
                                        }
                                    }
                                    let _ = collect_candidates(
                                        &body,
                                        env,
                                        var,
                                        &merged_defs,
                                        candidates,
                                    );
                                    for (param, prev) in saved {
                                        match prev {
                                            Some(v) => {
                                                env.insert(param, v);
                                            }
                                            None => {
                                                env.remove(&param);
                                            }
                                        };
                                    }
                                }
                            }
                        }
                    });
                }
                _ => {}
            }
        }

        _ => {}
    }
    Ok(())
}
