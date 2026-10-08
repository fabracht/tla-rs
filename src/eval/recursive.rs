use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Env, Expr, Value};

use super::Definitions;
use super::core::{STACK_GROWTH, STACK_RED_ZONE, eval};
use super::error::{EvalError, Result, value_type_name};
use super::helpers::apply_fn_value;

pub(crate) fn eval_fn_def_recursive(
    fn_name: &Arc<str>,
    param: &Arc<str>,
    domain: &[Value],
    body: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<BTreeMap<Value, Value>> {
    let memo: RefCell<BTreeMap<Value, Value>> = RefCell::new(BTreeMap::new());

    let prev = env.remove(param);
    for val in domain.iter() {
        if memo.borrow().contains_key(val) {
            continue;
        }
        env.insert(param.clone(), val.clone());
        let result = eval_with_memo(body, env, defs, fn_name, &memo)?;
        memo.borrow_mut().insert(val.clone(), result);
    }
    match prev {
        Some(old) => {
            env.insert(param.clone(), old);
        }
        None => {
            env.remove(param);
        }
    }

    Ok(memo.into_inner())
}

pub(crate) fn eval_with_memo(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    fn_name: &Arc<str>,
    memo: &RefCell<BTreeMap<Value, Value>>,
) -> Result<Value> {
    stacker::maybe_grow(STACK_RED_ZONE, STACK_GROWTH, || {
        eval_with_memo_inner(expr, env, defs, fn_name, memo)
    })
}

fn eval_with_memo_inner(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    fn_name: &Arc<str>,
    memo: &RefCell<BTreeMap<Value, Value>>,
) -> Result<Value> {
    match expr {
        Expr::FnApp(f, arg) => {
            if let Expr::Var(name) = f.as_ref()
                && name == fn_name
            {
                let av = eval_with_memo(arg, env, defs, fn_name, memo)?;
                if let Some(v) = memo.borrow().get(&av) {
                    return Ok(v.clone());
                }
                if let Some((params, fn_body)) = defs.get(name)
                    && params.is_empty()
                    && let Expr::FnDef(p, _, body) = fn_body.as_ref()
                {
                    let prev_p = env.insert(p.clone(), av.clone());
                    let result = eval_with_memo(body, env, defs, fn_name, memo)?;
                    match prev_p {
                        Some(old) => {
                            env.insert(p.clone(), old);
                        }
                        None => {
                            env.remove(p);
                        }
                    }
                    memo.borrow_mut().insert(av, result.clone());
                    return Ok(result);
                }
            }
            let fval = eval_with_memo(f, env, defs, fn_name, memo)?;
            let av = eval_with_memo(arg, env, defs, fn_name, memo)?;
            apply_fn_value(fval, av)
        }

        Expr::Let(var, binding, body) => {
            if let Some((params, op_body)) = super::ast_utils::parameterized_let_op(binding) {
                let mut local_defs = defs.clone();
                local_defs.insert(var.clone(), (params, Arc::new(op_body.clone())));
                return eval_with_memo(body, env, &local_defs, fn_name, memo);
            }
            if matches!(binding.as_ref(), Expr::FnDef(..))
                || super::ast_utils::is_operator_reference(binding, env, defs)
            {
                let mut local_defs = defs.clone();
                local_defs.insert(var.clone(), (vec![], Arc::new((**binding).clone())));
                return eval_with_memo(body, env, &local_defs, fn_name, memo);
            }
            let substituted =
                crate::substitution::substitute_expr(body, &[(var.clone(), (**binding).clone())]);
            eval_with_memo(&substituted, env, defs, fn_name, memo)
        }

        Expr::If(cond, then_br, else_br) => {
            let cv = eval_with_memo(cond, env, defs, fn_name, memo)?;
            match cv {
                Value::Bool(true) => eval_with_memo(then_br, env, defs, fn_name, memo),
                Value::Bool(false) => eval_with_memo(else_br, env, defs, fn_name, memo),
                _ => Err(EvalError::type_mismatch_ctx("Bool", cv, "IF condition")),
            }
        }

        Expr::Add(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, memo)?;
            match (lv, rv) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
                (a, b) => Err(EvalError::domain_error(format!(
                    "cannot add {} and {} (expected Int + Int)",
                    value_type_name(&a),
                    value_type_name(&b)
                ))),
            }
        }

        Expr::Eq(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, memo)?;
            Ok(Value::Bool(lv == rv))
        }

        Expr::SetMinus(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, memo)?;
            match (lv, rv) {
                (Value::Set(a), Value::Set(b)) => {
                    Ok(Value::set(a.difference(&b).cloned().collect()))
                }
                (a, b) => Err(EvalError::domain_error(format!(
                    "set minus requires Set \\ Set, got {} \\ {}",
                    value_type_name(&a),
                    value_type_name(&b)
                ))),
            }
        }

        Expr::SetEnum(elems) => {
            let mut result = BTreeSet::new();
            for e in elems {
                result.insert(eval_with_memo(e, env, defs, fn_name, memo)?);
            }
            Ok(Value::set(result))
        }

        Expr::Var(name) => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some((params, body)) = defs.get(name)
                && params.is_empty()
            {
                return eval_with_memo(body, env, defs, fn_name, memo);
            }
            Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
        }

        _ => eval(expr, env, defs),
    }
}
