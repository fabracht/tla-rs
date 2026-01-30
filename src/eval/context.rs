use super::core::eval;
use super::error::{EvalError, Result};
use super::global_state::EvalContext;
use super::helpers::{apply_fn_value, eval_set, flatten_fnapp_chain, in_set_symbolic};
use super::state::is_action_enabled;
use super::{Definitions, ResolvedInstances};
use crate::ast::{Env, Expr, Value};
use std::collections::BTreeSet;

pub fn eval_with_instances(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    instances: &ResolvedInstances,
) -> Result<Value> {
    match expr {
        Expr::QualifiedCall(instance, op, args) => {
            let instance_defs = instances.get(instance).ok_or_else(|| {
                EvalError::domain_error(format!("instance {} not found", instance))
            })?;

            let (params, body) = instance_defs.get(op).ok_or_else(|| {
                EvalError::domain_error(format!(
                    "operator {} not found in instance {}",
                    op, instance
                ))
            })?;

            if args.len() != params.len() {
                return Err(EvalError::domain_error(format!(
                    "{}!{} expects {} args, got {}",
                    instance,
                    op,
                    params.len(),
                    args.len()
                )));
            }

            let mut arg_vals = Vec::with_capacity(args.len());
            for arg_expr in args {
                arg_vals.push(eval_with_instances(arg_expr, env, defs, instances)?);
            }
            let mut prevs = Vec::with_capacity(params.len());
            for (param, val) in params.iter().zip(arg_vals) {
                prevs.push((param.clone(), env.insert(param.clone(), val)));
            }
            let result = eval_with_instances(body, env, defs, instances);
            for (param, prev) in prevs {
                match prev {
                    Some(old) => {
                        env.insert(param, old);
                    }
                    None => {
                        env.remove(&param);
                    }
                }
            }
            result
        }
        _ => eval(expr, env, defs),
    }
}

pub fn eval_with_context(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    ctx: &EvalContext,
) -> Result<Value> {
    match expr {
        Expr::EnabledOp(action) => {
            let enabled = is_action_enabled(
                action,
                &ctx.current_state,
                &ctx.state_vars,
                &ctx.constants,
                defs,
            )?;
            Ok(Value::Bool(enabled))
        }
        Expr::And(l, r) => {
            let lv = eval_bool_with_context(l, env, defs, ctx)?;
            if !lv {
                return Ok(Value::Bool(false));
            }
            let rv = eval_bool_with_context(r, env, defs, ctx)?;
            Ok(Value::Bool(rv))
        }
        Expr::Or(l, r) => {
            let lv = eval_bool_with_context(l, env, defs, ctx)?;
            if lv {
                return Ok(Value::Bool(true));
            }
            let rv = eval_bool_with_context(r, env, defs, ctx)?;
            Ok(Value::Bool(rv))
        }
        Expr::Not(e) => {
            let v = eval_bool_with_context(e, env, defs, ctx)?;
            Ok(Value::Bool(!v))
        }
        Expr::Implies(l, r) => {
            let lv = eval_bool_with_context(l, env, defs, ctx)?;
            if !lv {
                return Ok(Value::Bool(true));
            }
            let rv = eval_bool_with_context(r, env, defs, ctx)?;
            Ok(Value::Bool(rv))
        }
        Expr::If(cond, then_br, else_br) => {
            if eval_bool_with_context(cond, env, defs, ctx)? {
                eval_with_context(then_br, env, defs, ctx)
            } else {
                eval_with_context(else_br, env, defs, ctx)
            }
        }
        Expr::FnCall(name, args) => {
            if let Some((params, body)) = defs.get(name) {
                if args.len() != params.len() {
                    return Err(EvalError::domain_error(format!(
                        "function {} expects {} args, got {}",
                        name,
                        params.len(),
                        args.len()
                    )));
                }
                let mut arg_vals = Vec::with_capacity(args.len());
                for arg_expr in args {
                    arg_vals.push(eval_with_context(arg_expr, env, defs, ctx)?);
                }
                let mut prevs = Vec::with_capacity(params.len());
                for (param, val) in params.iter().zip(arg_vals) {
                    prevs.push((param.clone(), env.insert(param.clone(), val)));
                }
                let result = eval_with_context(body, env, defs, ctx);
                for (param, prev) in prevs {
                    match prev {
                        Some(old) => {
                            env.insert(param, old);
                        }
                        None => {
                            env.remove(&param);
                        }
                    }
                }
                result
            } else {
                eval(expr, env, defs)
            }
        }
        Expr::Var(name) => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some((params, body)) = defs.get(name)
                && params.is_empty()
            {
                return eval_with_context(body, env, defs, ctx);
            }
            Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
        }
        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let prev = env.remove(var);
            let mut holds = true;
            for val in dom {
                env.insert(var.clone(), val);
                if !eval_bool_with_context(body, env, defs, ctx)? {
                    holds = false;
                    break;
                }
            }
            match prev {
                Some(old) => {
                    env.insert(var.clone(), old);
                }
                None => {
                    env.remove(var);
                }
            }
            Ok(Value::Bool(holds))
        }
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let prev = env.remove(var);
            let mut found = false;
            for val in dom {
                env.insert(var.clone(), val);
                if eval_bool_with_context(body, env, defs, ctx)? {
                    found = true;
                    break;
                }
            }
            match prev {
                Some(old) => {
                    env.insert(var.clone(), old);
                }
                None => {
                    env.remove(var);
                }
            }
            Ok(Value::Bool(found))
        }
        Expr::In(elem, set) => {
            if matches!(set.as_ref(), Expr::Any) {
                return Ok(Value::Bool(true));
            }
            if let Expr::FunctionSet(domain_expr, codomain_expr) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Fn(f) = ev {
                    let domain = eval_set(domain_expr, env, defs)?;
                    let fn_domain: BTreeSet<Value> = f.keys().cloned().collect();
                    if fn_domain != domain {
                        return Ok(Value::Bool(false));
                    }
                    for val in f.values() {
                        if !in_set_symbolic(val, codomain_expr, env, defs)? {
                            return Ok(Value::Bool(false));
                        }
                    }
                    return Ok(Value::Bool(true));
                }
                return Ok(Value::Bool(false));
            }
            if let Expr::Powerset(inner) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Set(s) = ev {
                    let base = eval_set(inner, env, defs)?;
                    return Ok(Value::Bool(s.is_subset(&base)));
                }
                return Ok(Value::Bool(false));
            }
            if let Expr::SeqSet(domain_expr) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Tuple(seq) = ev {
                    let domain = eval_set(domain_expr, env, defs)?;
                    for e in &seq {
                        if !domain.contains(e) {
                            return Ok(Value::Bool(false));
                        }
                    }
                    return Ok(Value::Bool(true));
                }
                return Ok(Value::Bool(false));
            }
            let ev = eval_with_context(elem, env, defs, ctx)?;
            let sv = eval_set(set, env, defs)?;
            Ok(Value::Bool(sv.contains(&ev)))
        }
        Expr::NotIn(elem, set) => {
            if matches!(set.as_ref(), Expr::Any) {
                return Ok(Value::Bool(false));
            }
            if let Expr::FunctionSet(domain_expr, codomain_expr) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Fn(f) = ev {
                    let domain = eval_set(domain_expr, env, defs)?;
                    let fn_domain: BTreeSet<Value> = f.keys().cloned().collect();
                    if fn_domain != domain {
                        return Ok(Value::Bool(true));
                    }
                    for val in f.values() {
                        if !in_set_symbolic(val, codomain_expr, env, defs)? {
                            return Ok(Value::Bool(true));
                        }
                    }
                    return Ok(Value::Bool(false));
                }
                return Ok(Value::Bool(true));
            }
            if let Expr::Powerset(inner) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Set(s) = ev {
                    let base = eval_set(inner, env, defs)?;
                    return Ok(Value::Bool(!s.is_subset(&base)));
                }
                return Ok(Value::Bool(true));
            }
            if let Expr::SeqSet(domain_expr) = set.as_ref() {
                let ev = eval_with_context(elem, env, defs, ctx)?;
                if let Value::Tuple(seq) = ev {
                    let domain = eval_set(domain_expr, env, defs)?;
                    for e in &seq {
                        if !domain.contains(e) {
                            return Ok(Value::Bool(true));
                        }
                    }
                    return Ok(Value::Bool(false));
                }
                return Ok(Value::Bool(true));
            }
            let ev = eval_with_context(elem, env, defs, ctx)?;
            let sv = eval_set(set, env, defs)?;
            Ok(Value::Bool(!sv.contains(&ev)))
        }
        Expr::FnApp(f, arg) => {
            if let Expr::Lambda(params, body) = f.as_ref() {
                if params.len() != 1 {
                    return Err(EvalError::domain_error(format!(
                        "lambda expects {} args for [], got 1",
                        params.len()
                    )));
                }
                let av = eval_with_context(arg, env, defs, ctx)?;
                let prev = env.insert(params[0].clone(), av);
                let result = eval_with_context(body, env, defs, ctx);
                match prev {
                    Some(old) => {
                        env.insert(params[0].clone(), old);
                    }
                    None => {
                        env.remove(&params[0]);
                    }
                }
                return result;
            }
            let (base, keys) = flatten_fnapp_chain(expr);
            if keys.is_empty() {
                let fval = eval_with_context(f, env, defs, ctx)?;
                let av = eval_with_context(arg, env, defs, ctx)?;
                apply_fn_value(fval, av)
            } else {
                let mut current = eval_with_context(base, env, defs, ctx)?;
                for key_expr in keys {
                    let key = eval_with_context(key_expr, env, defs, ctx)?;
                    current = apply_fn_value(current, key)?;
                }
                Ok(current)
            }
        }
        Expr::Eq(l, r) => {
            let lv = eval_with_context(l, env, defs, ctx)?;
            let rv = eval_with_context(r, env, defs, ctx)?;
            Ok(Value::Bool(lv == rv))
        }
        Expr::Neq(l, r) => {
            let lv = eval_with_context(l, env, defs, ctx)?;
            let rv = eval_with_context(r, env, defs, ctx)?;
            Ok(Value::Bool(lv != rv))
        }
        _ => eval(expr, env, defs),
    }
}

pub(crate) fn eval_bool_with_context(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    ctx: &EvalContext,
) -> Result<bool> {
    match eval_with_context(expr, env, defs, ctx)? {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: other,
            context: None,
            span: None,
        }),
    }
}
