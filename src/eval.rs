use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Env, Expr, State, Value};
use crate::checker::format_value;

pub type Definitions = BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>;

#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVar(Arc<str>),
    TypeMismatch { expected: &'static str, got: Value },
    DivisionByZero,
    EmptyChoose,
    DomainError(String),
}

type Result<T> = std::result::Result<T, EvalError>;

pub fn eval(expr: &Expr, env: &Env, defs: &Definitions) -> Result<Value> {
    match expr {
        Expr::Lit(v) => Ok(v.clone()),

        Expr::Var(name) => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            if let Some((params, body)) = defs.get(name)
                && params.is_empty()
            {
                return eval(body, env, defs);
            }
            Err(EvalError::UndefinedVar(name.clone()))
        }

        Expr::Prime(name) => {
            let primed: Arc<str> = format!("{}'", name).into();
            env.get(&primed)
                .cloned()
                .ok_or(EvalError::UndefinedVar(primed))
        }

        Expr::And(l, r) => {
            let lv = eval_bool(l, env, defs)?;
            if !lv {
                return Ok(Value::Bool(false));
            }
            let rv = eval_bool(r, env, defs)?;
            Ok(Value::Bool(rv))
        }

        Expr::Or(l, r) => {
            let lv = eval_bool(l, env, defs)?;
            if lv {
                return Ok(Value::Bool(true));
            }
            let rv = eval_bool(r, env, defs)?;
            Ok(Value::Bool(rv))
        }

        Expr::Not(e) => {
            let v = eval_bool(e, env, defs)?;
            Ok(Value::Bool(!v))
        }

        Expr::Implies(l, r) => {
            let lv = eval_bool(l, env, defs)?;
            if !lv {
                return Ok(Value::Bool(true));
            }
            let rv = eval_bool(r, env, defs)?;
            Ok(Value::Bool(rv))
        }

        Expr::Equiv(l, r) => {
            let lv = eval_bool(l, env, defs)?;
            let rv = eval_bool(r, env, defs)?;
            Ok(Value::Bool(lv == rv))
        }

        Expr::Eq(l, r) => {
            let lv = eval(l, env, defs)?;
            let rv = eval(r, env, defs)?;
            Ok(Value::Bool(lv == rv))
        }

        Expr::Neq(l, r) => {
            let lv = eval(l, env, defs)?;
            let rv = eval(r, env, defs)?;
            Ok(Value::Bool(lv != rv))
        }

        Expr::In(elem, set) => {
            if let Expr::FunctionSet(domain_expr, codomain_expr) = set.as_ref() {
                let ev = eval(elem, env, defs)?;
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
                let ev = eval(elem, env, defs)?;
                if let Value::Set(s) = ev {
                    let base = eval_set(inner, env, defs)?;
                    return Ok(Value::Bool(s.is_subset(&base)));
                }
                return Ok(Value::Bool(false));
            }
            if let Expr::SeqSet(domain_expr) = set.as_ref() {
                let ev = eval(elem, env, defs)?;
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
            let ev = eval(elem, env, defs)?;
            let sv = eval_set(set, env, defs)?;
            Ok(Value::Bool(sv.contains(&ev)))
        }

        Expr::NotIn(elem, set) => {
            if let Expr::FunctionSet(domain_expr, codomain_expr) = set.as_ref() {
                let ev = eval(elem, env, defs)?;
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
                let ev = eval(elem, env, defs)?;
                if let Value::Set(s) = ev {
                    let base = eval_set(inner, env, defs)?;
                    return Ok(Value::Bool(!s.is_subset(&base)));
                }
                return Ok(Value::Bool(true));
            }
            if let Expr::SeqSet(domain_expr) = set.as_ref() {
                let ev = eval(elem, env, defs)?;
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
            let ev = eval(elem, env, defs)?;
            let sv = eval_set(set, env, defs)?;
            Ok(Value::Bool(!sv.contains(&ev)))
        }

        Expr::Add(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Int(lv + rv))
        }

        Expr::Sub(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Int(lv - rv))
        }

        Expr::Mul(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Int(lv * rv))
        }

        Expr::Div(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            if rv == 0 {
                return Err(EvalError::DivisionByZero);
            }
            Ok(Value::Int(lv / rv))
        }

        Expr::Mod(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            if rv == 0 {
                return Err(EvalError::DivisionByZero);
            }
            Ok(Value::Int(lv % rv))
        }

        Expr::Exp(base, exp) => {
            let b = eval_int(base, env, defs)?;
            let e = eval_int(exp, env, defs)?;
            if e < 0 {
                return Err(EvalError::DomainError("negative exponent".into()));
            }
            Ok(Value::Int(b.pow(e as u32)))
        }

        Expr::Neg(e) => {
            let v = eval_int(e, env, defs)?;
            Ok(Value::Int(-v))
        }

        Expr::Lt(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Bool(lv < rv))
        }

        Expr::Le(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Bool(lv <= rv))
        }

        Expr::Gt(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Bool(lv > rv))
        }

        Expr::Ge(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Bool(lv >= rv))
        }

        Expr::SetEnum(elems) => {
            let mut set = BTreeSet::new();
            for e in elems {
                set.insert(eval(e, env, defs)?);
            }
            Ok(Value::Set(set))
        }

        Expr::SetRange(lo, hi) => {
            let l = eval_int(lo, env, defs)?;
            let h = eval_int(hi, env, defs)?;
            let set: BTreeSet<Value> = (l..=h).map(Value::Int).collect();
            Ok(Value::Set(set))
        }

        Expr::SetFilter(var, domain, predicate) => {
            let domain_vals = eval_set(domain, env, defs)?;
            let mut result = BTreeSet::new();
            for val in domain_vals {
                let mut new_env = env.clone();
                new_env.insert(var.clone(), val.clone());
                if eval_bool(predicate, &new_env, defs)? {
                    result.insert(val);
                }
            }
            Ok(Value::Set(result))
        }

        Expr::SetMap(var, domain, body) => {
            let domain_vals = eval_set(domain, env, defs)?;
            let mut result = BTreeSet::new();
            for val in domain_vals {
                let mut new_env = env.clone();
                new_env.insert(var.clone(), val);
                result.insert(eval(body, &new_env, defs)?);
            }
            Ok(Value::Set(result))
        }

        Expr::Union(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::Set(ls.union(&rs).cloned().collect()))
        }

        Expr::Intersect(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::Set(ls.intersection(&rs).cloned().collect()))
        }

        Expr::SetMinus(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::Set(ls.difference(&rs).cloned().collect()))
        }

        Expr::Cartesian(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            let mut result = BTreeSet::new();
            for lv in &ls {
                for rv in &rs {
                    result.insert(Value::Tuple(vec![lv.clone(), rv.clone()]));
                }
            }
            Ok(Value::Set(result))
        }

        Expr::Subset(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::Bool(ls.is_subset(&rs)))
        }

        Expr::ProperSubset(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::Bool(ls.is_subset(&rs) && ls != rs))
        }

        Expr::Powerset(e) => {
            let s = eval_set(e, env, defs)?;
            let elements: Vec<_> = s.into_iter().collect();
            let n = elements.len();
            if n > 20 {
                return Err(EvalError::DomainError(format!(
                    "SUBSET of set with {} elements is too large (max 20)",
                    n
                )));
            }
            let mut result = BTreeSet::new();
            for mask in 0..(1u64 << n) {
                let mut subset = BTreeSet::new();
                for (i, elem) in elements.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        subset.insert(elem.clone());
                    }
                }
                result.insert(Value::Set(subset));
            }
            Ok(Value::Set(result))
        }

        Expr::Cardinality(e) => {
            let s = eval_set(e, env, defs)?;
            Ok(Value::Int(s.len() as i64))
        }

        Expr::IsFiniteSet(e) => {
            let _ = eval_set(e, env, defs)?;
            Ok(Value::Bool(true))
        }

        Expr::BigUnion(e) => {
            let outer = eval_set(e, env, defs)?;
            let mut result = BTreeSet::new();
            for val in outer {
                if let Value::Set(inner) = val {
                    for v in inner {
                        result.insert(v);
                    }
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Set",
                        got: val,
                    });
                }
            }
            Ok(Value::Set(result))
        }

        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            for val in dom {
                let mut local = env.clone();
                local.insert(var.clone(), val);
                if eval_bool(body, &local, defs)? {
                    return Ok(Value::Bool(true));
                }
            }
            Ok(Value::Bool(false))
        }

        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            for val in dom {
                let mut local = env.clone();
                local.insert(var.clone(), val);
                if !eval_bool(body, &local, defs)? {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::Choose(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            for val in &dom {
                let mut local = env.clone();
                local.insert(var.clone(), val.clone());
                if eval_bool(body, &local, defs)? {
                    return Ok(val.clone());
                }
            }
            if dom.is_empty()
                && let Expr::NotIn(_, set_expr) = body.as_ref()
            {
                let excluded = eval_set(set_expr, env, defs)?;
                for i in 0..1000 {
                    let candidate = Value::Str(format!("MODEL_VALUE_{}", i).into());
                    if !excluded.contains(&candidate) {
                        return Ok(candidate);
                    }
                }
            }
            Err(EvalError::EmptyChoose)
        }

        Expr::FnApp(f, arg) => {
            if let Expr::Lambda(params, body) = f.as_ref() {
                if params.len() != 1 {
                    return Err(EvalError::DomainError(format!(
                        "lambda expects {} args for [], got 1",
                        params.len()
                    )));
                }
                let av = eval(arg, env, defs)?;
                let mut local = env.clone();
                local.insert(params[0].clone(), av);
                return eval(body, &local, defs);
            }
            let fval = eval(f, env, defs)?;
            let av = eval(arg, env, defs)?;
            match fval {
                Value::Fn(fv) => fv
                    .get(&av)
                    .cloned()
                    .ok_or_else(|| EvalError::DomainError("key not in function domain".into())),
                Value::Tuple(tv) => {
                    if let Value::Int(idx) = av {
                        let i = idx as usize;
                        if i >= 1 && i <= tv.len() {
                            Ok(tv[i - 1].clone())
                        } else {
                            Err(EvalError::DomainError(format!(
                                "tuple index {} out of bounds",
                                idx
                            )))
                        }
                    } else {
                        Err(EvalError::TypeMismatch {
                            expected: "Int",
                            got: av,
                        })
                    }
                }
                other => Err(EvalError::TypeMismatch {
                    expected: "Fn or Tuple",
                    got: other,
                }),
            }
        }

        Expr::Lambda(_params, _body) => {
            Err(EvalError::DomainError(
                "lambda expression cannot be evaluated directly; must be applied".into(),
            ))
        }

        Expr::FnDef(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let mut result = BTreeMap::new();
            for val in dom {
                let mut local = env.clone();
                local.insert(var.clone(), val.clone());
                let out = eval(body, &local, defs)?;
                result.insert(val, out);
            }
            Ok(Value::Fn(result))
        }

        Expr::FnCall(name, args) => {
            if let Some((params, body)) = defs.get(name) {
                if args.len() != params.len() {
                    return Err(EvalError::DomainError(format!(
                        "function {} expects {} args, got {}",
                        name,
                        params.len(),
                        args.len()
                    )));
                }
                let mut local = env.clone();
                for (param, arg_expr) in params.iter().zip(args) {
                    let arg_val = eval(arg_expr, env, defs)?;
                    local.insert(param.clone(), arg_val);
                }
                eval(body, &local, defs)
            } else {
                Err(EvalError::UndefinedVar(name.clone()))
            }
        }

        Expr::FnMerge(left, right) => {
            let lv = eval(left, env, defs)?;
            let rv = eval(right, env, defs)?;
            match (lv, rv) {
                (Value::Fn(mut lf), Value::Fn(rf)) => {
                    for (k, v) in rf {
                        lf.entry(k).or_insert(v);
                    }
                    Ok(Value::Fn(lf))
                }
                (l, r) => Err(EvalError::TypeMismatch {
                    expected: "Fn @@ Fn",
                    got: Value::Tuple(vec![l, r]),
                }),
            }
        }

        Expr::SingleFn(key, val) => {
            let k = eval(key, env, defs)?;
            let v = eval(val, env, defs)?;
            let mut f = BTreeMap::new();
            f.insert(k, v);
            Ok(Value::Fn(f))
        }

        Expr::CustomOp(name, _left, _right) => {
            Err(EvalError::DomainError(format!("undefined custom operator: \\{}", name)))
        }

        Expr::Except(f, updates) => {
            let base = eval(f, env, defs)?;
            let mut result = base.clone();

            for (keys, val) in updates {
                let mut key_vals = Vec::new();
                for k in keys {
                    key_vals.push(eval(k, env, defs)?);
                }

                let old_val = get_nested(&base, &key_vals)?;
                let mut new_env = env.clone();
                new_env.insert("@".into(), old_val);
                let v = eval(val, &new_env, defs)?;

                match &mut result {
                    Value::Record(rec) => {
                        if let [Value::Str(field)] = key_vals.as_slice() {
                            rec.insert(field.clone(), v);
                        } else {
                            return Err(EvalError::DomainError(
                                "invalid record update path".to_string(),
                            ));
                        }
                    }
                    Value::Fn(fv) => {
                        update_nested(fv, &key_vals, v)?;
                    }
                    _ => {
                        return Err(EvalError::DomainError(
                            "EXCEPT requires record or function".to_string(),
                        ))
                    }
                }
            }
            Ok(result)
        }

        Expr::OldValue => {
            let at_key: Arc<str> = "@".into();
            env.get(&at_key)
                .cloned()
                .ok_or(EvalError::DomainError("@ used outside EXCEPT".to_string()))
        }

        Expr::Domain(f) => {
            let fv = eval_fn(f, env, defs)?;
            let dom: BTreeSet<Value> = fv.keys().cloned().collect();
            Ok(Value::Set(dom))
        }

        Expr::FunctionSet(domain, codomain) => {
            let dom = eval_set(domain, env, defs)?;
            let cod = eval_set(codomain, env, defs)?;

            fn enumerate_functions(
                keys: &[Value],
                codomain: &BTreeSet<Value>,
            ) -> Vec<BTreeMap<Value, Value>> {
                if keys.is_empty() {
                    return vec![BTreeMap::new()];
                }
                let key = &keys[0];
                let rest = &keys[1..];
                let sub_fns = enumerate_functions(rest, codomain);
                let mut result = Vec::new();
                for val in codomain {
                    for sub_fn in &sub_fns {
                        let mut f = sub_fn.clone();
                        f.insert(key.clone(), val.clone());
                        result.push(f);
                    }
                }
                result
            }

            let keys: Vec<Value> = dom.into_iter().collect();
            let functions = enumerate_functions(&keys, &cod);
            let set: BTreeSet<Value> = functions.into_iter().map(Value::Fn).collect();
            Ok(Value::Set(set))
        }

        Expr::RecordLit(fields) => {
            let mut rec = BTreeMap::new();
            for (name, expr) in fields {
                rec.insert(name.clone(), eval(expr, env, defs)?);
            }
            Ok(Value::Record(rec))
        }

        Expr::RecordSet(fields) => {
            let mut field_domains: Vec<(Arc<str>, Vec<Value>)> = Vec::new();
            for (name, domain_expr) in fields {
                let domain = eval_set(domain_expr, env, defs)?;
                field_domains.push((name.clone(), domain.into_iter().collect()));
            }
            let result = cartesian_product_records(&field_domains);
            Ok(Value::Set(result.into_iter().map(Value::Record).collect()))
        }

        Expr::RecordAccess(rec, field) => {
            let rv = eval_record(rec, env, defs)?;
            rv.get(field)
                .cloned()
                .ok_or_else(|| EvalError::DomainError(format!("field '{}' not in record", field)))
        }

        Expr::TupleLit(elems) => {
            let mut tup = Vec::new();
            for e in elems {
                tup.push(eval(e, env, defs)?);
            }
            Ok(Value::Tuple(tup))
        }

        Expr::TupleAccess(tup, idx) => {
            let tv = eval_tuple(tup, env, defs)?;
            tv.get(*idx)
                .cloned()
                .ok_or_else(|| EvalError::DomainError(format!("index {} out of bounds", idx)))
        }

        Expr::Len(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            Ok(Value::Int(tv.len() as i64))
        }

        Expr::Head(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            tv.first()
                .cloned()
                .ok_or_else(|| EvalError::DomainError("Head of empty sequence".into()))
        }

        Expr::Tail(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            if tv.is_empty() {
                return Err(EvalError::DomainError("Tail of empty sequence".into()));
            }
            Ok(Value::Tuple(tv[1..].to_vec()))
        }

        Expr::Append(seq, elem) => {
            let mut tv = eval_tuple(seq, env, defs)?;
            let ev = eval(elem, env, defs)?;
            tv.push(ev);
            Ok(Value::Tuple(tv))
        }

        Expr::Concat(seq1, seq2) => {
            let mut tv1 = eval_tuple(seq1, env, defs)?;
            let tv2 = eval_tuple(seq2, env, defs)?;
            tv1.extend(tv2);
            Ok(Value::Tuple(tv1))
        }

        Expr::SubSeq(seq, start, end) => {
            let tv = eval_tuple(seq, env, defs)?;
            let s = eval_int(start, env, defs)? as usize;
            let e = eval_int(end, env, defs)? as usize;
            if s < 1 || s > tv.len() + 1 || e < s - 1 || e > tv.len() {
                return Err(EvalError::DomainError("SubSeq index out of bounds".into()));
            }
            let subseq = tv.get((s - 1)..e).unwrap_or(&[]).to_vec();
            Ok(Value::Tuple(subseq))
        }

        Expr::SelectSeq(seq, test) => {
            let tv = eval_tuple(seq, env, defs)?;
            let mut result = Vec::new();
            for elem in tv {
                let keep = if let Expr::Lambda(params, body) = test.as_ref() {
                    if params.len() != 1 {
                        return Err(EvalError::DomainError(format!(
                            "SelectSeq test expects 1 parameter, got {}",
                            params.len()
                        )));
                    }
                    let mut local = env.clone();
                    local.insert(params[0].clone(), elem.clone());
                    eval_bool(body, &local, defs)?
                } else {
                    return Err(EvalError::DomainError(
                        "SelectSeq test must be a LAMBDA expression".into(),
                    ));
                };
                if keep {
                    result.push(elem);
                }
            }
            Ok(Value::Tuple(result))
        }

        Expr::SeqSet(_) => Err(EvalError::DomainError(
            "Seq(S) cannot be enumerated (infinite set); use for membership tests only".into(),
        )),

        Expr::Print(val, result) => {
            let v = eval(val, env, defs)?;
            eprintln!("[Print] {}", format_value(&v));
            eval(result, env, defs)
        }

        Expr::Assert(cond, msg) => {
            let c = eval_bool(cond, env, defs)?;
            if c {
                Ok(Value::Bool(true))
            } else {
                let m = eval(msg, env, defs)?;
                Err(EvalError::DomainError(format!(
                    "Assertion failed: {}",
                    format_value(&m)
                )))
            }
        }

        Expr::JavaTime => Err(EvalError::DomainError(
            "JavaTime is dumb, use SystemTime instead".into(),
        )),

        Expr::SystemTime => {
            use std::time::{SystemTime, UNIX_EPOCH};
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_millis() as i64)
                .unwrap_or(0);
            Ok(Value::Int(now))
        }

        Expr::Permutations(set_expr) => {
            let set = eval_set(set_expr, env, defs)?;
            let elements: Vec<Value> = set.into_iter().collect();
            let n = elements.len();
            if n > 10 {
                return Err(EvalError::DomainError(format!(
                    "Permutations of set with {} elements is too large (max 10)",
                    n
                )));
            }
            let perms = permutations(&elements);
            let result: BTreeSet<Value> = perms.into_iter().map(Value::Tuple).collect();
            Ok(Value::Set(result))
        }

        Expr::If(cond, then_br, else_br) => {
            if eval_bool(cond, env, defs)? {
                eval(then_br, env, defs)
            } else {
                eval(else_br, env, defs)
            }
        }

        Expr::Let(var, binding, body) => {
            let val = eval(binding, env, defs)?;
            let mut local = env.clone();
            local.insert(var.clone(), val);
            eval(body, &local, defs)
        }

        Expr::Case(branches) => {
            for (cond, result) in branches {
                if eval_bool(cond, env, defs)? {
                    return eval(result, env, defs);
                }
            }
            Err(EvalError::DomainError("no case matched".into()))
        }

        Expr::Unchanged(vars) => {
            for var in vars {
                let current = env
                    .get(var)
                    .ok_or_else(|| EvalError::UndefinedVar(var.clone()))?;
                let primed: Arc<str> = format!("{}'", var).into();
                let next = env.get(&primed).ok_or(EvalError::UndefinedVar(primed))?;
                if current != next {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }
    }
}

fn eval_bool(expr: &Expr, env: &Env, defs: &Definitions) -> Result<bool> {
    match eval(expr, env, defs)? {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: other,
        }),
    }
}

fn eval_int(expr: &Expr, env: &Env, defs: &Definitions) -> Result<i64> {
    match eval(expr, env, defs)? {
        Value::Int(i) => Ok(i),
        other => Err(EvalError::TypeMismatch {
            expected: "Int",
            got: other,
        }),
    }
}

fn in_set_symbolic(val: &Value, set_expr: &Expr, env: &Env, defs: &Definitions) -> Result<bool> {
    match set_expr {
        Expr::Powerset(inner) => {
            if let Value::Set(s) = val {
                let base = eval_set(inner, env, defs)?;
                Ok(s.is_subset(&base))
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
            if let Value::Tuple(seq) = val {
                let domain = eval_set(domain_expr, env, defs)?;
                for e in seq {
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

fn eval_set(expr: &Expr, env: &Env, defs: &Definitions) -> Result<BTreeSet<Value>> {
    match eval(expr, env, defs)? {
        Value::Set(s) => Ok(s),
        other => Err(EvalError::TypeMismatch {
            expected: "Set",
            got: other,
        }),
    }
}

fn eval_fn(expr: &Expr, env: &Env, defs: &Definitions) -> Result<BTreeMap<Value, Value>> {
    match eval(expr, env, defs)? {
        Value::Fn(f) => Ok(f),
        other => Err(EvalError::TypeMismatch {
            expected: "Fn",
            got: other,
        }),
    }
}

fn eval_record(expr: &Expr, env: &Env, defs: &Definitions) -> Result<BTreeMap<Arc<str>, Value>> {
    match eval(expr, env, defs)? {
        Value::Record(r) => Ok(r),
        other => Err(EvalError::TypeMismatch {
            expected: "Record",
            got: other,
        }),
    }
}

fn eval_tuple(expr: &Expr, env: &Env, defs: &Definitions) -> Result<Vec<Value>> {
    match eval(expr, env, defs)? {
        Value::Tuple(t) => Ok(t),
        other => Err(EvalError::TypeMismatch {
            expected: "Tuple",
            got: other,
        }),
    }
}

fn cartesian_product_records(
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

fn get_nested(base: &Value, keys: &[Value]) -> Result<Value> {
    if keys.is_empty() {
        return Ok(base.clone());
    }
    match (base, &keys[0]) {
        (Value::Record(rec), Value::Str(field)) => {
            let v = rec
                .get(field)
                .ok_or_else(|| EvalError::DomainError(format!("field '{}' not found", field)))?;
            get_nested(v, &keys[1..])
        }
        (Value::Fn(f), key) => {
            let v = f
                .get(key)
                .ok_or_else(|| EvalError::DomainError("key not in function domain".into()))?;
            get_nested(v, &keys[1..])
        }
        _ => Err(EvalError::DomainError("cannot access into this value".into())),
    }
}

fn update_nested(f: &mut BTreeMap<Value, Value>, keys: &[Value], val: Value) -> Result<()> {
    if keys.is_empty() {
        return Ok(());
    }
    if keys.len() == 1 {
        f.insert(keys[0].clone(), val);
        return Ok(());
    }
    let inner = f
        .get_mut(&keys[0])
        .ok_or_else(|| EvalError::DomainError("key not in function domain".into()))?;
    match inner {
        Value::Fn(inner_fn) => update_nested(inner_fn, &keys[1..], val),
        _ => Err(EvalError::TypeMismatch {
            expected: "Fn",
            got: inner.clone(),
        }),
    }
}

pub fn next_states(
    next: &Expr,
    current: &State,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Vec<State>> {
    let mut results = Vec::new();
    let mut base_env = state_to_env(current);
    for (k, v) in constants {
        base_env.insert(k.clone(), v.clone());
    }
    enumerate_next(next, &base_env, vars, 0, defs, &mut results)?;
    Ok(results)
}

fn state_to_env(state: &State) -> Env {
    state.vars.clone()
}

fn env_to_next_state(env: &Env, vars: &[Arc<str>]) -> State {
    let mut state = State::new();
    for var in vars {
        let primed: Arc<str> = format!("{}'", var).into();
        if let Some(val) = env.get(&primed) {
            state.vars.insert(var.clone(), val.clone());
        }
    }
    state
}

fn enumerate_next(
    next: &Expr,
    env: &Env,
    vars: &[Arc<str>],
    var_idx: usize,
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    if var_idx >= vars.len() {
        if eval_bool(next, env, defs)? {
            results.push(env_to_next_state(env, vars));
        }
        return Ok(());
    }

    let var = &vars[var_idx];
    let primed: Arc<str> = format!("{}'", var).into();

    let candidates = infer_candidates(next, env, var, defs)?;

    for candidate in candidates {
        let mut local = env.clone();
        local.insert(primed.clone(), candidate);
        enumerate_next(next, &local, vars, var_idx + 1, defs, results)?;
    }

    Ok(())
}

fn infer_candidates(next: &Expr, env: &Env, var: &Arc<str>, defs: &Definitions) -> Result<Vec<Value>> {
    let mut candidates = BTreeSet::new();
    collect_candidates(next, env, var, defs, &mut candidates)?;

    if candidates.is_empty()
        && let Some(current) = env.get(var) {
            candidates.insert(current.clone());
        }

    Ok(candidates.into_iter().collect())
}

fn collect_candidates(
    expr: &Expr,
    env: &Env,
    var: &Arc<str>,
    defs: &Definitions,
    candidates: &mut BTreeSet<Value>,
) -> Result<()> {
    match expr {
        Expr::Eq(l, r) => {
            if let Expr::Prime(name) = l.as_ref()
                && name == var
                    && let Ok(val) = eval(r, env, defs) {
                        candidates.insert(val);
                    }
            if let Expr::Prime(name) = r.as_ref()
                && name == var
                    && let Ok(val) = eval(l, env, defs) {
                        candidates.insert(val);
                    }
        }

        Expr::In(elem, set) => {
            if let Expr::Prime(name) = elem.as_ref()
                && name == var
                    && let Ok(s) = eval_set(set, env, defs) {
                        for val in s {
                            candidates.insert(val);
                        }
                    }
        }

        Expr::And(l, r) | Expr::Or(l, r) | Expr::Implies(l, r) | Expr::Equiv(l, r) => {
            collect_candidates(l, env, var, defs, candidates)?;
            collect_candidates(r, env, var, defs, candidates)?;
        }

        Expr::Exists(bound, domain, body) | Expr::Forall(bound, domain, body) => {
            if let Ok(dom) = eval_set(domain, env, defs) {
                for val in dom {
                    let mut local = env.clone();
                    local.insert(bound.clone(), val);
                    collect_candidates(body, &local, var, defs, candidates)?;
                }
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
                let mut local = env.clone();
                local.insert(bound.clone(), val);
                collect_candidates(body, &local, var, defs, candidates)?;
            }
        }

        Expr::Unchanged(vars) => {
            if vars.contains(var)
                && let Some(current) = env.get(var) {
                    candidates.insert(current.clone());
                }
        }

        _ => {}
    }
    Ok(())
}

pub fn init_states(init: &Expr, vars: &[Arc<str>], domains: &Env, defs: &Definitions) -> Result<Vec<State>> {
    let mut results = Vec::new();
    let initial_env = domains.clone();
    enumerate_init(init, &initial_env, vars, 0, domains, defs, &mut results)?;
    Ok(results)
}

fn enumerate_init(
    init: &Expr,
    env: &Env,
    vars: &[Arc<str>],
    var_idx: usize,
    domains: &Env,
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    if var_idx >= vars.len() {
        if eval_bool(init, env, defs)? {
            let mut state = State::new();
            for var in vars {
                if let Some(val) = env.get(var) {
                    state.vars.insert(var.clone(), val.clone());
                }
            }
            results.push(state);
        }
        return Ok(());
    }

    let var = &vars[var_idx];

    let candidates = match domains.get(var) {
        Some(Value::Set(s)) => s.iter().cloned().collect::<Vec<_>>(),
        _ => infer_init_candidates(init, env, var, defs)?,
    };

    for candidate in candidates {
        let mut local = env.clone();
        local.insert(var.clone(), candidate);
        enumerate_init(init, &local, vars, var_idx + 1, domains, defs, results)?;
    }

    Ok(())
}

fn infer_init_candidates(init: &Expr, env: &Env, var: &Arc<str>, defs: &Definitions) -> Result<Vec<Value>> {
    let mut candidates = BTreeSet::new();

    fn collect(
        expr: &Expr,
        env: &Env,
        var: &Arc<str>,
        defs: &Definitions,
        candidates: &mut BTreeSet<Value>,
    ) -> Result<()> {
        match expr {
            Expr::Eq(l, r) => {
                if let Expr::Var(name) = l.as_ref()
                    && name == var
                        && let Ok(val) = eval(r, env, defs) {
                            candidates.insert(val);
                        }
                if let Expr::Var(name) = r.as_ref()
                    && name == var
                        && let Ok(val) = eval(l, env, defs) {
                            candidates.insert(val);
                        }
            }
            Expr::In(elem, set) => {
                if let Expr::Var(name) = elem.as_ref()
                    && name == var
                        && let Ok(Value::Set(s)) = eval(set, env, defs) {
                            for val in s {
                                candidates.insert(val);
                            }
                        }
            }
            Expr::And(l, r) | Expr::Or(l, r) => {
                collect(l, env, var, defs, candidates)?;
                collect(r, env, var, defs, candidates)?;
            }
            _ => {}
        }
        Ok(())
    }

    collect(init, env, var, defs, &mut candidates)?;
    Ok(candidates.into_iter().collect())
}

fn permutations(elements: &[Value]) -> Vec<Vec<Value>> {
    if elements.is_empty() {
        return vec![vec![]];
    }
    let mut result = Vec::new();
    for (i, elem) in elements.iter().enumerate() {
        let mut rest: Vec<Value> = elements[..i].to_vec();
        rest.extend(elements[i + 1..].iter().cloned());
        for mut perm in permutations(&rest) {
            perm.insert(0, elem.clone());
            result.push(perm);
        }
    }
    result
}
