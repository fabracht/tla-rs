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

trait CandidateTarget {
    fn match_var(&self, name: &Arc<str>) -> Option<usize>;
    fn insert(&mut self, idx: usize, val: Value);
    fn var_at(&self, idx: usize) -> &Arc<str>;
}

struct SingleVarTarget<'a> {
    var: &'a Arc<str>,
    candidates: &'a mut BTreeSet<Value>,
}

impl CandidateTarget for SingleVarTarget<'_> {
    fn match_var(&self, name: &Arc<str>) -> Option<usize> {
        if name == self.var { Some(0) } else { None }
    }

    fn insert(&mut self, _idx: usize, val: Value) {
        self.candidates.insert(val);
    }

    fn var_at(&self, _idx: usize) -> &Arc<str> {
        self.var
    }
}

struct AllVarsTarget<'a> {
    vars: &'a [Arc<str>],
    all_candidates: &'a mut [BTreeSet<Value>],
}

impl CandidateTarget for AllVarsTarget<'_> {
    fn match_var(&self, name: &Arc<str>) -> Option<usize> {
        self.vars.iter().position(|v| v == name)
    }

    fn insert(&mut self, idx: usize, val: Value) {
        self.all_candidates[idx].insert(val);
    }

    fn var_at(&self, idx: usize) -> &Arc<str> {
        &self.vars[idx]
    }
}

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

fn try_indexed_prime_candidate<T: CandidateTarget>(
    prime_side: &Expr,
    value_side: &Expr,
    env: &mut Env,
    defs: &Definitions,
    target: &mut T,
) {
    if let Some((name, path)) = extract_indexed_prime(prime_side)
        && !path.is_empty()
        && let Some(idx) = target.match_var(&name)
    {
        let key_vals: Option<Vec<Value>> = path.iter().map(|p| eval(p, env, defs).ok()).collect();
        if let Some(keys) = key_vals
            && let Ok(new_val) = eval(value_side, env, defs)
            && let Some(current) = env.get(target.var_at(idx))
            && let Some(updated) = apply_update(current, &keys, new_val)
        {
            target.insert(idx, updated);
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
                if *idx <= 0 || *idx as usize > tup.len() {
                    return None;
                }
                let idx = *idx as usize;
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
    let mut target = SingleVarTarget {
        var,
        candidates: &mut candidates,
    };
    collect_candidates_impl(next, env, defs, &mut target)?;

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

pub(crate) fn infer_all_candidates(
    next: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    defs: &Definitions,
) -> Result<Vec<Vec<Value>>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut all_candidates: Vec<BTreeSet<Value>> = vec![BTreeSet::new(); vars.len()];
    let mut target = AllVarsTarget {
        vars,
        all_candidates: &mut all_candidates,
    };
    collect_candidates_impl(next, env, defs, &mut target)?;

    for (i, var) in vars.iter().enumerate() {
        if all_candidates[i].is_empty()
            && let Some(current) = env.get(var)
        {
            all_candidates[i].insert(current.clone());
        }
    }

    let result = all_candidates
        .into_iter()
        .map(|s| s.into_iter().collect())
        .collect();

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.infer_candidates_time_ns += _start.elapsed().as_nanos();
        stats.infer_candidates_calls += vars.len() as u64;
    });

    Ok(result)
}

fn restore_env(env: &mut Env, saved: Vec<(Arc<str>, Option<Value>)>) {
    for (param, prev) in saved {
        match prev {
            Some(v) => env.insert(param, v),
            None => env.remove(&param),
        };
    }
}

fn bind_params(
    params: &[Arc<str>],
    args: &[Expr],
    env: &mut Env,
    defs: &Definitions,
) -> Vec<(Arc<str>, Option<Value>)> {
    let mut saved = Vec::new();
    for (param, arg) in params.iter().zip(args.iter()) {
        if let Ok(val) = eval(arg, env, defs) {
            let prev = env.insert(param.clone(), val);
            saved.push((param.clone(), prev));
        }
    }
    saved
}

fn collect_candidates_impl<T: CandidateTarget>(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    target: &mut T,
) -> Result<()> {
    match expr {
        Expr::Eq(l, r) => {
            if let Expr::Prime(name) = l.as_ref()
                && let Some(idx) = target.match_var(name)
                && let Ok(val) = eval(r, env, defs)
            {
                target.insert(idx, val);
            }
            if let Expr::Prime(name) = r.as_ref()
                && let Some(idx) = target.match_var(name)
                && let Ok(val) = eval(l, env, defs)
            {
                target.insert(idx, val);
            }
            try_indexed_prime_candidate(l, r, env, defs, target);
            try_indexed_prime_candidate(r, l, env, defs, target);
        }

        Expr::In(elem, set) => {
            if let Expr::Prime(name) = elem.as_ref()
                && let Some(idx) = target.match_var(name)
                && let Ok(s) = eval_set(set, env, defs)
            {
                for val in s {
                    target.insert(idx, val);
                }
            }
        }

        Expr::And(l, r) | Expr::Or(l, r) | Expr::Implies(l, r) | Expr::Equiv(l, r) => {
            if contains_prime_ref(l, defs) {
                collect_candidates_impl(l, env, defs, target)?;
            }
            if contains_prime_ref(r, defs) {
                collect_candidates_impl(r, env, defs, target)?;
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
                    collect_candidates_impl(body, env, defs, target)?;
                }
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
            }
        }

        Expr::If(_, then_br, else_br) => {
            collect_candidates_impl(then_br, env, defs, target)?;
            collect_candidates_impl(else_br, env, defs, target)?;
        }

        Expr::Case(branches) => {
            for (_, result) in branches {
                collect_candidates_impl(result, env, defs, target)?;
            }
        }

        Expr::Let(bound, binding, body) => {
            if let Ok(val) = eval(binding, env, defs) {
                let bound = bound.clone();
                let prev = env.insert(bound.clone(), val);
                collect_candidates_impl(body, env, defs, target)?;
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
            }
        }

        Expr::Unchanged(vars) => {
            let expanded = super::core::expand_unchanged_vars(vars, defs);
            for var in &expanded {
                if let Some(idx) = target.match_var(var)
                    && let Some(current) = env.get(var)
                {
                    target.insert(idx, current.clone());
                }
            }
        }

        Expr::FnCall(name, args) => {
            if let Some((params, body)) = defs.get(name)
                && params.len() == args.len()
                && contains_prime_ref(body, defs)
            {
                let params: Vec<Arc<str>> = params.clone();
                let saved = bind_params(&params, args, env, defs);
                collect_candidates_impl(body, env, defs, target)?;
                restore_env(env, saved);
            }
        }

        Expr::LabeledAction(_, action) => {
            collect_candidates_impl(action, env, defs, target)?;
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
                            let saved = bind_params(&params, args, env, defs);
                            let _ = collect_candidates_impl(body, env, &merged_defs, target);
                            restore_env(env, saved);
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
                                    let saved = bind_params(&params, args, env, defs);
                                    let _ =
                                        collect_candidates_impl(&body, env, &merged_defs, target);
                                    restore_env(env, saved);
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
