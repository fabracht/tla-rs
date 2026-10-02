use super::core::eval;
use super::error::{EvalError, Result};
use super::global_state::{EvalContext, with_enabled_vars};
use super::{Definitions, ResolvedInstances};
use crate::ast::{Env, Expr, Value};

pub fn eval_with_instances(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    instances: &ResolvedInstances,
) -> Result<Value> {
    match expr {
        Expr::QualifiedCall(instance_expr, op, args) => {
            let Expr::Var(instance_name) = instance_expr.as_ref() else {
                return Err(EvalError::domain_error(
                    "eval_with_instances only supports static instance names",
                ));
            };
            let instance_defs = instances.get(instance_name).ok_or_else(|| {
                EvalError::domain_error(format!("instance {} not found", instance_name))
            })?;

            let (params, body) = instance_defs.get(op).ok_or_else(|| {
                EvalError::domain_error(format!(
                    "operator {} not found in instance {}",
                    op, instance_name
                ))
            })?;

            if args.len() != params.len() {
                return Err(EvalError::domain_error(format!(
                    "{}!{} expects {} args, got {}",
                    instance_name,
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

/// `expr` where `ENABLED` may appear: it reads the current values of
/// `ctx.state_vars` from `env`.
pub fn eval_with_context(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    ctx: &EvalContext,
) -> Result<Value> {
    with_enabled_vars(&ctx.state_vars, || eval(expr, env, defs))
}
