use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Env, Expr, Value};
use crate::checker::format_value;

use super::Definitions;
use super::core::eval;
use super::error::{EvalError, Result, value_type_name};

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
        let result = eval_with_memo(body, env, defs, fn_name, param, domain, &memo)?;
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

#[allow(clippy::only_used_in_recursion)]
pub(crate) fn eval_with_memo(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    fn_name: &Arc<str>,
    fn_param: &Arc<str>,
    fn_domain: &[Value],
    memo: &RefCell<BTreeMap<Value, Value>>,
) -> Result<Value> {
    match expr {
        Expr::FnApp(f, arg) => {
            if let Expr::Var(name) = f.as_ref()
                && name == fn_name
            {
                let av = eval_with_memo(arg, env, defs, fn_name, fn_param, fn_domain, memo)?;
                if let Some(v) = memo.borrow().get(&av) {
                    return Ok(v.clone());
                }
                if let Some((params, fn_body)) = defs.get(name)
                    && params.is_empty()
                    && let Expr::FnDef(p, _, body) = fn_body
                {
                    let prev_p = env.insert(p.clone(), av.clone());
                    let result =
                        eval_with_memo(body, env, defs, fn_name, fn_param, fn_domain, memo)?;
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
            let fval = eval_with_memo(f, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let av = eval_with_memo(arg, env, defs, fn_name, fn_param, fn_domain, memo)?;
            match fval {
                Value::Fn(fv) => fv.get(&av).cloned().ok_or_else(|| {
                    EvalError::domain_error(format!(
                        "key {} not in function domain",
                        format_value(&av)
                    ))
                }),
                Value::Tuple(tv) => {
                    if let Value::Int(idx) = av {
                        let i = idx as usize;
                        if i >= 1 && i <= tv.len() {
                            Ok(tv[i - 1].clone())
                        } else {
                            Err(EvalError::domain_error(format!(
                                "sequence index {} out of bounds (sequence has {} elements)",
                                idx,
                                tv.len()
                            )))
                        }
                    } else {
                        Err(EvalError::TypeMismatch {
                            expected: "Int",
                            got: av,
                            context: Some("sequence index"),
                            span: None,
                        })
                    }
                }
                other => Err(EvalError::type_mismatch_ctx(
                    "Fn or Sequence",
                    other,
                    "function application",
                )),
            }
        }

        Expr::Let(var, binding, body) => {
            let mut local_defs = defs.clone();
            local_defs.insert(var.clone(), (vec![], (**binding).clone()));
            eval_with_memo(body, env, &local_defs, fn_name, fn_param, fn_domain, memo)
        }

        Expr::If(cond, then_br, else_br) => {
            let cv = eval_with_memo(cond, env, defs, fn_name, fn_param, fn_domain, memo)?;
            match cv {
                Value::Bool(true) => {
                    eval_with_memo(then_br, env, defs, fn_name, fn_param, fn_domain, memo)
                }
                Value::Bool(false) => {
                    eval_with_memo(else_br, env, defs, fn_name, fn_param, fn_domain, memo)
                }
                _ => Err(EvalError::type_mismatch_ctx("Bool", cv, "IF condition")),
            }
        }

        Expr::Add(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, fn_param, fn_domain, memo)?;
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
            let lv = eval_with_memo(l, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, fn_param, fn_domain, memo)?;
            Ok(Value::Bool(lv == rv))
        }

        Expr::SetMinus(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, fn_param, fn_domain, memo)?;
            match (lv, rv) {
                (Value::Set(a), Value::Set(b)) => {
                    Ok(Value::Set(a.difference(&b).cloned().collect()))
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
                result.insert(eval_with_memo(
                    e, env, defs, fn_name, fn_param, fn_domain, memo,
                )?);
            }
            Ok(Value::Set(result))
        }

        Expr::Var(name) => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some((params, body)) = defs.get(name)
                && params.is_empty()
            {
                return eval_with_memo(body, env, defs, fn_name, fn_param, fn_domain, memo);
            }
            Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
        }

        _ => eval(expr, env, defs),
    }
}
