use super::Definitions;
use super::core::eval;
use super::error::{EvalError, Result};
use crate::ast::{Env, Expr, Value};
use crate::checker::format_value;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

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
        Value::Record(rec) => {
            if let Value::Str(field) = &key {
                rec.get(field).cloned().ok_or_else(|| {
                    EvalError::domain_error(format!(
                        "key {} not in function domain",
                        format_value(&key)
                    ))
                })
            } else {
                Err(EvalError::TypeMismatch {
                    expected: "Str",
                    got: key,
                    context: Some("record field"),
                    span: None,
                })
            }
        }
        other => Err(EvalError::TypeMismatch {
            expected: "Fn, Tuple or Record",
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

pub(crate) fn value_in_function_set(
    val: &Value,
    domain_expr: &Expr,
    codomain_expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<bool> {
    let Some(val_domain) = val.function_domain() else {
        return Ok(false);
    };
    let domain = eval_set(domain_expr, env, defs)?;
    if val_domain != domain {
        return Ok(false);
    }
    let entries = val
        .as_function_map()
        .expect("function_domain succeeded, so the value is a function");
    for v in entries.values() {
        if !in_set_symbolic(v, codomain_expr, env, defs)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn is_structural_set_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Powerset(_) | Expr::FunctionSet(_, _) | Expr::SeqSet(_) | Expr::RecordSet(_)
    )
}

enum ResolvedDomain<'a> {
    Concrete(BTreeSet<Value>),
    Symbolic(&'a Expr),
}

impl<'a> ResolvedDomain<'a> {
    fn resolve(expr: &'a Expr, env: &mut Env, defs: &Definitions) -> Result<Self> {
        if matches!(expr, Expr::Any) || is_structural_set_expr(expr) {
            Ok(ResolvedDomain::Symbolic(expr))
        } else {
            Ok(ResolvedDomain::Concrete(eval_set(expr, env, defs)?))
        }
    }

    fn contains(&self, val: &Value, env: &mut Env, defs: &Definitions) -> Result<bool> {
        match self {
            ResolvedDomain::Concrete(s) => Ok(s.contains(val)),
            ResolvedDomain::Symbolic(e) => in_set_symbolic(val, e, env, defs),
        }
    }
}

pub(crate) fn in_set_symbolic(
    val: &Value,
    set_expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<bool> {
    match set_expr {
        Expr::Any => Ok(true),
        Expr::Powerset(inner) => {
            if let Value::Set(s) = val {
                let inner_domain = ResolvedDomain::resolve(inner, env, defs)?;
                for member in s.iter() {
                    if !inner_domain.contains(member, env, defs)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Expr::FunctionSet(domain_expr, codomain_expr) => {
            value_in_function_set(val, domain_expr, codomain_expr, env, defs)
        }
        Expr::SeqSet(domain_expr) => {
            let seq = match val {
                Value::Tuple(t) => Some(t.as_ref().clone()),
                Value::Fn(f) => fn_as_tuple(f),
                _ => None,
            };
            if let Some(seq) = seq {
                let domain = ResolvedDomain::resolve(domain_expr, env, defs)?;
                for e in &seq {
                    if !domain.contains(e, env, defs)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Expr::RecordSet(fields) => {
            if let Value::Record(r) = val {
                if r.len() != fields.len() {
                    return Ok(false);
                }
                for (name, type_expr) in fields {
                    match r.get(name) {
                        Some(field_val) => {
                            if !in_set_symbolic(field_val, type_expr, env, defs)? {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false),
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
        Value::Set(s) => Ok(Arc::unwrap_or_clone(s)),
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
    let v = eval(expr, env, defs)?;
    match v.as_function_map() {
        Some(m) => Ok(m),
        None => Err(EvalError::TypeMismatch {
            expected: "Fn",
            got: v,
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
        Value::Record(r) => Ok(Arc::unwrap_or_clone(r)),
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
        let v = f.get(&Value::Int(i as i64))?;
        result.push(v.clone());
    }
    Some(result)
}

pub(crate) fn eval_tuple(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<Vec<Value>> {
    match eval(expr, env, defs)? {
        Value::Tuple(t) => Ok(Arc::unwrap_or_clone(t)),
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
        (Value::Tuple(t), Value::Int(idx)) => {
            let v = tuple_element(t, *idx)?;
            get_nested(v, &keys[1..])
        }
        _ => Err(EvalError::domain_error("cannot access into this value")),
    }
}

fn tuple_index(len: usize, idx: i64) -> Result<usize> {
    if idx < 1 || idx as usize > len {
        return Err(EvalError::domain_error(format!(
            "sequence index {} out of bounds (sequence has {} elements)",
            idx, len
        )));
    }
    Ok((idx - 1) as usize)
}

fn tuple_element(t: &[Value], idx: i64) -> Result<&Value> {
    Ok(&t[tuple_index(t.len(), idx)?])
}

pub(crate) fn update_nested_value(base: &Value, keys: &[Value], val: Value) -> Result<Value> {
    if keys.is_empty() {
        return Ok(val);
    }
    match base {
        Value::Fn(f) => {
            let mut m = (**f).clone();
            let inner = if keys.len() == 1 {
                val
            } else {
                let prev = m.get(&keys[0]).ok_or_else(|| {
                    EvalError::domain_error(format!(
                        "key {} not in function domain",
                        format_value(&keys[0])
                    ))
                })?;
                update_nested_value(prev, &keys[1..], val)?
            };
            m.insert(keys[0].clone(), inner);
            Ok(Value::func(m))
        }
        Value::Record(rec) => {
            let Value::Str(field) = &keys[0] else {
                return Err(EvalError::domain_error(format!(
                    "expected string key for record field, got {}",
                    format_value(&keys[0])
                )));
            };
            let mut m = (**rec).clone();
            let inner = if keys.len() == 1 {
                val
            } else {
                let prev = m.get(field).ok_or_else(|| {
                    EvalError::domain_error(format!("field '{}' not found in record", field))
                })?;
                update_nested_value(prev, &keys[1..], val)?
            };
            m.insert(field.clone(), inner);
            Ok(Value::record(m))
        }
        Value::Tuple(t) => {
            let Value::Int(idx) = &keys[0] else {
                return Err(EvalError::domain_error(format!(
                    "expected integer index for sequence, got {}",
                    format_value(&keys[0])
                )));
            };
            let mut v = (**t).clone();
            let pos = tuple_index(v.len(), *idx)?;
            v[pos] = if keys.len() == 1 {
                val
            } else {
                update_nested_value(&v[pos], &keys[1..], val)?
            };
            Ok(Value::tuple(v))
        }
        _ => Err(EvalError::TypeMismatch {
            expected: "Fn, Record or Tuple",
            got: base.clone(),
            context: Some("nested EXCEPT update"),
            span: None,
        }),
    }
}
