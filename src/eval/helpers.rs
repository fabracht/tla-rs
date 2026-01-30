use super::Definitions;
use super::core::eval;
use super::error::{EvalError, Result};
use crate::ast::{Env, Expr, Value};
use crate::checker::format_value;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub(crate) fn flatten_fnapp_chain(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut keys = Vec::new();
    let mut current = expr;
    while let Expr::FnApp(f, arg) = current {
        if matches!(f.as_ref(), Expr::Lambda(..)) {
            break;
        }
        keys.push(arg.as_ref());
        current = f.as_ref();
    }
    keys.reverse();
    (current, keys)
}

pub(crate) fn apply_fn_value(fval: Value, key: Value) -> Result<Value> {
    match fval {
        Value::Fn(fv) => fv.get(&key).cloned().ok_or_else(|| {
            EvalError::domain_error(format!("key {} not in function domain", format_value(&key)))
        }),
        Value::Tuple(tv) => {
            if let Value::Int(idx) = key {
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
                    got: key,
                    context: Some("sequence index"),
                    span: None,
                })
            }
        }
        other => Err(EvalError::TypeMismatch {
            expected: "Fn or Tuple",
            got: other,
            context: Some("function application"),
            span: None,
        }),
    }
}

pub(crate) fn eval_bool(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<bool> {
    match eval(expr, env, defs)? {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn eval_int(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<i64> {
    match eval(expr, env, defs)? {
        Value::Int(i) => Ok(i),
        other => Err(EvalError::TypeMismatch {
            expected: "Int",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn in_set_symbolic(
    val: &Value,
    set_expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<bool> {
    match set_expr {
        Expr::Powerset(inner) => {
            if let Value::Set(s) = val {
                for member in s {
                    if !in_set_symbolic(member, inner, env, defs)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Expr::FunctionSet(domain_expr, codomain_expr) => {
            if let Value::Fn(f) = val {
                let domain = eval_set(domain_expr, env, defs)?;
                let fn_domain: BTreeSet<Value> = f.keys().cloned().collect();
                if fn_domain != domain {
                    return Ok(false);
                }
                for v in f.values() {
                    if !in_set_symbolic(v, codomain_expr, env, defs)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Expr::SeqSet(domain_expr) => {
            let seq = match val {
                Value::Tuple(t) => Some(t.clone()),
                Value::Fn(f) => fn_as_tuple(f),
                _ => None,
            };
            if let Some(seq) = seq {
                let domain = eval_set(domain_expr, env, defs)?;
                for e in &seq {
                    if !domain.contains(e) {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        _ => {
            let set = eval_set(set_expr, env, defs)?;
            Ok(set.contains(val))
        }
    }
}

pub(crate) fn eval_set(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<BTreeSet<Value>> {
    match eval(expr, env, defs)? {
        Value::Set(s) => Ok(s),
        other => Err(EvalError::TypeMismatch {
            expected: "Set",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn eval_fn(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<BTreeMap<Value, Value>> {
    match eval(expr, env, defs)? {
        Value::Fn(f) => Ok(f),
        other => Err(EvalError::TypeMismatch {
            expected: "Fn",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn eval_record(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<BTreeMap<Arc<str>, Value>> {
    match eval(expr, env, defs)? {
        Value::Record(r) => Ok(r),
        other => Err(EvalError::TypeMismatch {
            expected: "Record",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn fn_as_tuple(f: &BTreeMap<Value, Value>) -> Option<Vec<Value>> {
    let n = f.len();
    let mut result = Vec::with_capacity(n);
    for i in 1..=n {
        match f.get(&Value::Int(i as i64)) {
            Some(v) => result.push(v.clone()),
            None => return None,
        }
    }
    Some(result)
}

pub(crate) fn eval_tuple(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<Vec<Value>> {
    match eval(expr, env, defs)? {
        Value::Tuple(t) => Ok(t),
        Value::Fn(f) => fn_as_tuple(&f).ok_or(EvalError::TypeMismatch {
            expected: "Tuple",
            got: Value::Fn(f),
            context: None,
            span: None,
        }),
        other => Err(EvalError::TypeMismatch {
            expected: "Tuple",
            got: other,
            context: None,
            span: None,
        }),
    }
}

pub(crate) fn cartesian_product_records(
    fields: &[(Arc<str>, Vec<Value>)],
) -> Vec<BTreeMap<Arc<str>, Value>> {
    if fields.is_empty() {
        return vec![BTreeMap::new()];
    }
    let (name, values) = &fields[0];
    let rest = cartesian_product_records(&fields[1..]);
    let mut result = Vec::new();
    for v in values {
        for rec in &rest {
            let mut new_rec = rec.clone();
            new_rec.insert(name.clone(), v.clone());
            result.push(new_rec);
        }
    }
    result
}

pub(crate) fn get_nested(base: &Value, keys: &[Value]) -> Result<Value> {
    if keys.is_empty() {
        return Ok(base.clone());
    }
    match (base, &keys[0]) {
        (Value::Record(rec), Value::Str(field)) => {
            let v = rec
                .get(field)
                .ok_or_else(|| EvalError::domain_error(format!("field '{}' not found", field)))?;
            get_nested(v, &keys[1..])
        }
        (Value::Fn(f), key) => {
            let v = f.get(key).ok_or_else(|| {
                EvalError::domain_error(format!("key {} not in function domain", format_value(key)))
            })?;
            get_nested(v, &keys[1..])
        }
        _ => Err(EvalError::domain_error("cannot access into this value")),
    }
}

pub(crate) fn update_nested(
    f: &mut BTreeMap<Value, Value>,
    keys: &[Value],
    val: Value,
) -> Result<()> {
    if keys.is_empty() {
        return Ok(());
    }
    if keys.len() == 1 {
        f.insert(keys[0].clone(), val);
        return Ok(());
    }
    let inner = f.get_mut(&keys[0]).ok_or_else(|| {
        EvalError::domain_error(format!(
            "key {} not in function domain",
            format_value(&keys[0])
        ))
    })?;
    match inner {
        Value::Fn(inner_fn) => update_nested(inner_fn, &keys[1..], val),
        _ => Err(EvalError::TypeMismatch {
            expected: "Fn",
            got: inner.clone(),
            context: Some("nested EXCEPT update"),
            span: None,
        }),
    }
}
