use super::Definitions;
use super::combinatorics::{
    detect_cardinality_constraint, enumerate_subbags, generate_subsets_with_constraint,
    permutations,
};
use super::error::{EvalError, Result};
#[cfg(feature = "profiling")]
use super::global_state::PROFILING_STATS;
use super::global_state::{
    CHECKER_STATS, PARAMETERIZED_INSTANCES, RESOLVED_INSTANCES, RNG, TLC_STATE,
};
use super::helpers::{
    apply_fn_value, cartesian_product_records, eval_bool, eval_fn, eval_int, eval_record, eval_set,
    eval_tuple, fn_as_tuple, get_nested, in_set_symbolic, is_structural_set_expr,
    update_nested_value,
};
use super::recursive::eval_fn_def_recursive;
use crate::ast::{Env, Expr, Value};
use crate::checker::format_value;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub fn eval(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<Value> {
    stacker::maybe_grow(32 * 1024, 1024 * 1024, || eval_inner(expr, env, defs))
}

pub(crate) fn expand_unchanged_vars(vars: &[Arc<str>], defs: &Definitions) -> Vec<Arc<str>> {
    let mut result = Vec::new();
    for var in vars {
        if let Some((params, body)) = defs.get(var)
            && params.is_empty()
            && let Expr::TupleLit(elems) = body
            && elems.iter().all(|e| matches!(e, Expr::Var(_)))
        {
            for elem in elems {
                if let Expr::Var(name) = elem {
                    result.push(name.clone());
                }
            }
            continue;
        }
        result.push(var.clone());
    }
    result
}

fn eval_inner(expr: &Expr, env: &mut Env, defs: &Definitions) -> Result<Value> {
    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| s.borrow_mut().eval_calls += 1);

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
            Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
        }

        Expr::Prime(name) => {
            let primed = crate::intern::primed_name(name);
            env.get(&primed)
                .cloned()
                .ok_or_else(|| EvalError::undefined_var_with_env(primed, env, defs))
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
            let ev = eval(elem, env, defs)?;
            Ok(Value::Bool(in_set_symbolic(&ev, set, env, defs)?))
        }

        Expr::NotIn(elem, set) => {
            let ev = eval(elem, env, defs)?;
            Ok(Value::Bool(!in_set_symbolic(&ev, set, env, defs)?))
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
                return Err(EvalError::division_by_zero());
            }
            Ok(Value::Int(lv / rv))
        }

        Expr::Mod(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            if rv == 0 {
                return Err(EvalError::division_by_zero());
            }
            Ok(Value::Int(lv % rv))
        }

        Expr::BitwiseAnd(l, r) => {
            let lv = eval_int(l, env, defs)?;
            let rv = eval_int(r, env, defs)?;
            Ok(Value::Int(lv & rv))
        }

        Expr::TransitiveClosure(rel_expr) => {
            let rel = eval_set(rel_expr, env, defs)?;
            let mut result = rel.clone();
            let mut changed = true;
            while changed {
                changed = false;
                let pairs: Vec<_> = result.iter().cloned().collect();
                for p1 in &pairs {
                    for p2 in &pairs {
                        if let (Value::Tuple(t1), Value::Tuple(t2)) = (p1, p2)
                            && t1.len() == 2
                            && t2.len() == 2
                            && t1[1] == t2[0]
                        {
                            let new_pair = Value::tuple(vec![t1[0].clone(), t2[1].clone()]);
                            if !result.contains(&new_pair) {
                                result.insert(new_pair);
                                changed = true;
                            }
                        }
                    }
                }
            }
            Ok(Value::set(result))
        }

        Expr::ReflexiveTransitiveClosure(rel_expr) => {
            let rel = eval_set(rel_expr, env, defs)?;
            let mut result = rel.clone();
            let mut changed = true;
            while changed {
                changed = false;
                let pairs: Vec<_> = result.iter().cloned().collect();
                for p1 in &pairs {
                    for p2 in &pairs {
                        if let (Value::Tuple(t1), Value::Tuple(t2)) = (p1, p2)
                            && t1.len() == 2
                            && t2.len() == 2
                            && t1[1] == t2[0]
                        {
                            let new_pair = Value::tuple(vec![t1[0].clone(), t2[1].clone()]);
                            if !result.contains(&new_pair) {
                                result.insert(new_pair);
                                changed = true;
                            }
                        }
                    }
                }
            }
            for pair in result.clone() {
                if let Value::Tuple(t) = pair
                    && t.len() == 2
                {
                    result.insert(Value::tuple(vec![t[0].clone(), t[0].clone()]));
                    result.insert(Value::tuple(vec![t[1].clone(), t[1].clone()]));
                }
            }
            Ok(Value::set(result))
        }

        Expr::ActionCompose(_, _) => Err(EvalError::domain_error(
            "action composition (\\cdot) cannot be evaluated in explicit-state model checking",
        )),

        Expr::Exp(base, exp) => {
            let b = eval_int(base, env, defs)?;
            let e = eval_int(exp, env, defs)?;
            if e < 0 {
                return Err(EvalError::domain_error("negative exponent"));
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
            Ok(Value::set(set))
        }

        Expr::SetRange(lo, hi) => {
            let l = eval_int(lo, env, defs)?;
            let h = eval_int(hi, env, defs)?;
            let set: BTreeSet<Value> = (l..=h).map(Value::Int).collect();
            Ok(Value::set(set))
        }

        Expr::SetFilter(var, domain, predicate) => {
            if let Expr::Powerset(inner) = domain.as_ref()
                && let Some(constraint) = detect_cardinality_constraint(predicate, var, env, defs)
            {
                let base_set = eval_set(inner, env, defs)?;
                let elements: Vec<_> = base_set.into_iter().collect();
                return Ok(Value::set(generate_subsets_with_constraint(
                    &elements, constraint,
                )));
            }

            let domain_vals = eval_set(domain, env, defs)?;
            let mut result = BTreeSet::new();
            let prev = env.remove(var);
            for val in domain_vals {
                env.insert(var.clone(), val.clone());
                if eval_bool(predicate, env, defs)? {
                    result.insert(val);
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
            Ok(Value::set(result))
        }

        Expr::SetMap(var, domain, body) => {
            let domain_vals = eval_set(domain, env, defs)?;
            let mut result = BTreeSet::new();
            let prev = env.remove(var);
            for val in domain_vals {
                env.insert(var.clone(), val);
                result.insert(eval(body, env, defs)?);
            }
            match prev {
                Some(old) => {
                    env.insert(var.clone(), old);
                }
                None => {
                    env.remove(var);
                }
            }
            Ok(Value::set(result))
        }

        Expr::Union(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::set(ls.union(&rs).cloned().collect()))
        }

        Expr::Intersect(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::set(ls.intersection(&rs).cloned().collect()))
        }

        Expr::SetMinus(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            Ok(Value::set(ls.difference(&rs).cloned().collect()))
        }

        Expr::Cartesian(l, r) => {
            let ls = eval_set(l, env, defs)?;
            let rs = eval_set(r, env, defs)?;
            let mut result = BTreeSet::new();
            for lv in &ls {
                for rv in &rs {
                    result.insert(Value::tuple(vec![lv.clone(), rv.clone()]));
                }
            }
            Ok(Value::set(result))
        }

        Expr::Subset(l, r) => {
            if is_structural_set_expr(r) {
                let ls = eval_set(l, env, defs)?;
                for elem in &ls {
                    if !in_set_symbolic(elem, r, env, defs)? {
                        return Ok(Value::Bool(false));
                    }
                }
                return Ok(Value::Bool(true));
            }
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
                return Err(EvalError::domain_error(format!(
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
                result.insert(Value::set(subset));
            }
            Ok(Value::set(result))
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
                    for v in Arc::unwrap_or_clone(inner) {
                        result.insert(v);
                    }
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Set",
                        got: val,
                        context: Some("UNION element"),
                        span: None,
                    });
                }
            }
            Ok(Value::set(result))
        }

        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let prev = env.remove(var);
            let mut found = false;
            for val in dom {
                env.insert(var.clone(), val);
                let b = eval_bool(body, env, defs)?;
                if b {
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

        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let prev = env.remove(var);
            let mut holds = true;
            for val in dom {
                env.insert(var.clone(), val);
                if !eval_bool(body, env, defs)? {
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

        Expr::Choose(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let prev = env.remove(var);
            let mut chosen = None;
            for val in &dom {
                env.insert(var.clone(), val.clone());
                if eval_bool(body, env, defs)? {
                    chosen = Some(val.clone());
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
            if let Some(v) = chosen {
                return Ok(v);
            }
            Err(EvalError::empty_choose())
        }

        Expr::ChooseUnbounded(var, body) => {
            match try_eval_unbounded_choose(var, body, env, defs)? {
                Some(v) => Ok(v),
                None => Err(EvalError::domain_error(format!(
                    "unbounded CHOOSE {} : P only supports `{} \\notin S` and `{} = e` patterns",
                    var, var, var
                ))),
            }
        }

        Expr::FnApp(f, arg) => {
            if let Expr::Lambda(params, body) = f.as_ref() {
                if params.len() != 1 {
                    return Err(EvalError::domain_error(format!(
                        "lambda expects {} args for [], got 1",
                        params.len()
                    )));
                }
                let av = eval(arg, env, defs)?;
                let prev = env.insert(params[0].clone(), av);
                let result = eval(body, env, defs);
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
            let fval = eval(f, env, defs)?;
            let av = eval(arg, env, defs)?;
            apply_fn_value(fval, av)
        }

        Expr::Lambda(_params, _body) => Err(EvalError::domain_error(
            "lambda expression cannot be evaluated directly; must be applied",
        )),

        Expr::FnDef(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let dom_vec: Vec<_> = dom.into_iter().collect();
            let placeholder_name: Arc<str> = "".into();
            let result = eval_fn_def_recursive(&placeholder_name, var, &dom_vec, body, env, defs)?;
            Ok(Value::func(result))
        }

        Expr::FnCall(name, args) => {
            match name.as_ref() {
                "BitAnd" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "BitAnd expects 2 args, got {}",
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a & b));
                }
                "BitOr" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "BitOr expects 2 args, got {}",
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a | b));
                }
                "BitXor" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "BitXor expects 2 args, got {}",
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a ^ b));
                }
                "BitNot" => {
                    if args.len() != 1 {
                        return Err(EvalError::domain_error(format!(
                            "BitNot expects 1 arg, got {}",
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    return Ok(Value::Int(!a));
                }
                "ShiftLeft" | "LeftShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "{} expects 2 args, got {}",
                            name,
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::domain_error(format!(
                            "shift amount {} out of range (0-63)",
                            b
                        )));
                    }
                    return Ok(Value::Int(a << b));
                }
                "ShiftRight" | "RightShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "{} expects 2 args, got {}",
                            name,
                            args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::domain_error(format!(
                            "shift amount {} out of range (0-63)",
                            b
                        )));
                    }
                    return Ok(Value::Int(a >> b));
                }
                _ => {}
            }
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
                    arg_vals.push(eval(arg_expr, env, defs)?);
                }
                let mut prevs = Vec::with_capacity(params.len());
                for (param, val) in params.iter().zip(arg_vals) {
                    prevs.push((param.clone(), env.insert(param.clone(), val)));
                }
                let result = eval(body, env, defs);
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
                Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
            }
        }

        Expr::FnMerge(left, right) => {
            let lv = eval(left, env, defs)?;
            let rv = eval(right, env, defs)?;
            match (lv.as_function_map(), rv.as_function_map()) {
                (Some(mut lf), Some(rf)) => {
                    for (k, v) in rf {
                        lf.entry(k).or_insert(v);
                    }
                    Ok(Value::func(lf))
                }
                _ => Err(EvalError::TypeMismatch {
                    expected: "Fn @@ Fn",
                    got: Value::tuple(vec![lv, rv]),
                    context: Some("function merge"),
                    span: None,
                }),
            }
        }

        Expr::SingleFn(key, val) => {
            let k = eval(key, env, defs)?;
            let v = eval(val, env, defs)?;
            let mut f = BTreeMap::new();
            f.insert(k, v);
            Ok(Value::func(f))
        }

        Expr::CustomOp(name, _left, _right) => Err(EvalError::domain_error(format!(
            "undefined custom operator: \\{}",
            name
        ))),

        Expr::Except(f, updates) => {
            let base = eval(f, env, defs)?;
            let mut result = base.clone();

            for (keys, val) in updates {
                let mut key_vals = Vec::new();
                for k in keys {
                    key_vals.push(eval(k, env, defs)?);
                }

                let old_val = get_nested(&result, &key_vals)?;
                let at_key: Arc<str> = "@".into();
                let prev_at = env.insert(at_key.clone(), old_val);
                let v = eval(val, env, defs)?;
                match prev_at {
                    Some(old) => {
                        env.insert(at_key, old);
                    }
                    None => {
                        env.remove(&at_key);
                    }
                }

                if !result.is_function() {
                    return Err(EvalError::domain_error(
                        "EXCEPT requires a record, function or sequence",
                    ));
                }
                result = update_nested_value(&result, &key_vals, v)?;
            }
            Ok(result)
        }

        Expr::OldValue => {
            let at_key: Arc<str> = "@".into();
            env.get(&at_key)
                .cloned()
                .ok_or(EvalError::domain_error("@ used outside EXCEPT".to_string()))
        }

        Expr::Domain(f) => {
            let fv = eval(f, env, defs)?;
            match fv {
                Value::Fn(fmap) => {
                    let dom: BTreeSet<Value> = fmap.keys().cloned().collect();
                    Ok(Value::set(dom))
                }
                Value::Tuple(seq) => {
                    let dom: BTreeSet<Value> =
                        (1..=seq.len()).map(|i| Value::Int(i as i64)).collect();
                    Ok(Value::set(dom))
                }
                Value::Record(rec) => {
                    let dom: BTreeSet<Value> = rec.keys().map(|f| Value::Str(f.clone())).collect();
                    Ok(Value::set(dom))
                }
                other => Err(EvalError::type_mismatch_ctx(
                    "Fn, Sequence or Record",
                    other,
                    "DOMAIN",
                )),
            }
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
            let set: BTreeSet<Value> = functions
                .into_iter()
                .map(|f| fn_as_tuple(&f).map(Value::tuple).unwrap_or(Value::func(f)))
                .collect();
            Ok(Value::set(set))
        }

        Expr::RecordLit(fields) => {
            let mut rec = BTreeMap::new();
            for (name, expr) in fields {
                rec.insert(name.clone(), eval(expr, env, defs)?);
            }
            Ok(Value::record(rec))
        }

        Expr::RecordSet(fields) => {
            let mut field_domains: Vec<(Arc<str>, Vec<Value>)> = Vec::new();
            for (name, domain_expr) in fields {
                let domain = eval_set(domain_expr, env, defs)?;
                field_domains.push((name.clone(), domain.into_iter().collect()));
            }
            let result = cartesian_product_records(&field_domains);
            Ok(Value::set(result.into_iter().map(Value::record).collect()))
        }

        Expr::RecordAccess(rec, field) => {
            let rv = eval_record(rec, env, defs)?;
            rv.get(field)
                .cloned()
                .ok_or_else(|| EvalError::domain_error(format!("field '{}' not in record", field)))
        }

        Expr::TupleLit(elems) => {
            let mut tup = Vec::new();
            for e in elems {
                tup.push(eval(e, env, defs)?);
            }
            Ok(Value::tuple(tup))
        }

        Expr::TupleAccess(tup, idx) => {
            let v = eval(tup, env, defs)?;
            match v {
                Value::Tuple(tv) => tv.get(*idx).cloned().ok_or_else(|| {
                    EvalError::domain_error(format!(
                        "sequence index {} out of bounds (sequence has {} elements)",
                        idx + 1,
                        tv.len()
                    ))
                }),
                Value::Fn(fv) => {
                    let key = Value::Int((*idx + 1) as i64);
                    fv.get(&key).cloned().ok_or_else(|| {
                        EvalError::domain_error(format!("key {} not in function domain", idx + 1))
                    })
                }
                other => Err(EvalError::TypeMismatch {
                    expected: "Tuple or Fn",
                    got: other,
                    context: Some("tuple access"),
                    span: None,
                }),
            }
        }

        Expr::Len(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            Ok(Value::Int(tv.len() as i64))
        }

        Expr::Head(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            tv.first()
                .cloned()
                .ok_or_else(|| EvalError::domain_error("Head of empty sequence"))
        }

        Expr::Tail(seq) => {
            let tv = eval_tuple(seq, env, defs)?;
            if tv.is_empty() {
                return Err(EvalError::domain_error("Tail of empty sequence"));
            }
            Ok(Value::tuple(tv[1..].to_vec()))
        }

        Expr::Append(seq, elem) => {
            let mut tv = eval_tuple(seq, env, defs)?;
            let ev = eval(elem, env, defs)?;
            tv.push(ev);
            Ok(Value::tuple(tv))
        }

        Expr::Concat(seq1, seq2) => {
            let mut tv1 = eval_tuple(seq1, env, defs)?;
            let tv2 = eval_tuple(seq2, env, defs)?;
            tv1.extend(tv2);
            Ok(Value::tuple(tv1))
        }

        Expr::SubSeq(seq, start, end) => {
            let tv = eval_tuple(seq, env, defs)?;
            let s = eval_int(start, env, defs)? as usize;
            let e = eval_int(end, env, defs)? as usize;
            if s < 1 || s > tv.len() + 1 || e < s - 1 || e > tv.len() {
                return Err(EvalError::domain_error("SubSeq index out of bounds"));
            }
            let subseq = tv.get((s - 1)..e).unwrap_or(&[]).to_vec();
            Ok(Value::tuple(subseq))
        }

        Expr::SelectSeq(seq, test) => {
            let tv = eval_tuple(seq, env, defs)?;
            let mut result = Vec::new();
            for elem in tv {
                let keep = if let Expr::Lambda(params, body) = test.as_ref() {
                    if params.len() != 1 {
                        return Err(EvalError::domain_error(format!(
                            "SelectSeq test expects 1 parameter, got {}",
                            params.len()
                        )));
                    }
                    let prev = env.insert(params[0].clone(), elem.clone());
                    let b = eval_bool(body, env, defs)?;
                    match prev {
                        Some(old) => {
                            env.insert(params[0].clone(), old);
                        }
                        None => {
                            env.remove(&params[0]);
                        }
                    }
                    b
                } else {
                    return Err(EvalError::domain_error(
                        "SelectSeq test must be a LAMBDA expression",
                    ));
                };
                if keep {
                    result.push(elem);
                }
            }
            Ok(Value::tuple(result))
        }

        Expr::SeqSet(_) => Err(EvalError::domain_error(
            "Seq(S) cannot be enumerated (infinite set); use for membership tests only",
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
                Err(EvalError::domain_error(format!(
                    "Assertion failed: {}",
                    format_value(&m)
                )))
            }
        }

        Expr::JavaTime => Err(EvalError::domain_error(
            "JavaTime is dumb, use SystemTime instead",
        )),

        Expr::SystemTime => {
            #[cfg(not(target_arch = "wasm32"))]
            {
                use std::time::{SystemTime, UNIX_EPOCH};
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|d| d.as_millis() as i64)
                    .unwrap_or(0);
                Ok(Value::Int(now))
            }
            #[cfg(target_arch = "wasm32")]
            {
                Ok(Value::Int(0))
            }
        }

        Expr::Permutations(set_expr) => {
            let set = eval_set(set_expr, env, defs)?;
            let elements: Vec<Value> = set.into_iter().collect();
            let n = elements.len();
            if n > 10 {
                return Err(EvalError::domain_error(format!(
                    "Permutations of set with {} elements is too large (max 10)",
                    n
                )));
            }
            let perms = permutations(&elements);
            let result: BTreeSet<Value> = perms.into_iter().map(Value::tuple).collect();
            Ok(Value::set(result))
        }

        Expr::SortSeq(seq_expr, cmp_expr) => {
            let tv = eval_tuple(seq_expr, env, defs)?;
            let mut result = tv;
            if let Expr::Lambda(params, body) = cmp_expr.as_ref() {
                if params.len() != 2 {
                    return Err(EvalError::domain_error(
                        "SortSeq comparator must take exactly 2 arguments",
                    ));
                }
                let param_a = &params[0];
                let param_b = &params[1];
                let mut local = env.clone();
                result.sort_by(|a, b| {
                    local.insert(param_a.clone(), a.clone());
                    local.insert(param_b.clone(), b.clone());
                    match eval_bool(body, &mut local, defs) {
                        Ok(true) => std::cmp::Ordering::Less,
                        Ok(false) => std::cmp::Ordering::Greater,
                        Err(_) => std::cmp::Ordering::Equal,
                    }
                });
            } else {
                return Err(EvalError::domain_error(
                    "SortSeq comparator must be a LAMBDA expression",
                ));
            }
            Ok(Value::tuple(result))
        }

        Expr::PrintT(val) => {
            let v = eval(val, env, defs)?;
            eprintln!("[Print] {}", format_value(&v));
            Ok(Value::Bool(true))
        }

        Expr::TLCToString(val) => {
            let v = eval(val, env, defs)?;
            Ok(Value::Str(format_value(&v).into()))
        }

        Expr::RandomElement(set_expr) => {
            let set = eval_set(set_expr, env, defs)?;
            if set.is_empty() {
                return Err(EvalError::domain_error("RandomElement of empty set"));
            }
            let elements: Vec<_> = set.into_iter().collect();
            let idx = RNG.with(|rng| rng.borrow_mut().usize(..elements.len()));
            elements
                .into_iter()
                .nth(idx)
                .ok_or_else(|| EvalError::domain_error("random element index out of bounds"))
        }

        Expr::TLCGet(idx_expr) => {
            let key = eval(idx_expr, env, defs)?;
            match key {
                Value::Int(idx) => TLC_STATE.with(|state| {
                    Ok(state
                        .borrow()
                        .get(&idx)
                        .cloned()
                        .unwrap_or(Value::Bool(false)))
                }),
                Value::Str(s) => CHECKER_STATS.with(|stats| {
                    let stats = stats.borrow();
                    match s.as_ref() {
                        "distinct" => Ok(Value::Int(stats.distinct)),
                        "level" => Ok(Value::Int(stats.level)),
                        "diameter" => Ok(Value::Int(stats.diameter)),
                        "queue" => Ok(Value::Int(stats.queue)),
                        "duration" => Ok(Value::Int(stats.duration)),
                        "generated" => Ok(Value::Int(stats.generated)),
                        other => Err(EvalError::domain_error(format!(
                            "TLCGet: unknown key \"{}\"",
                            other
                        ))),
                    }
                }),
                other => Err(EvalError::TypeMismatch {
                    expected: "Int or Str",
                    got: other,
                    context: Some("TLCGet key"),
                    span: None,
                }),
            }
        }

        Expr::TLCSet(idx_expr, val_expr) => {
            let idx = eval_int(idx_expr, env, defs)?;
            let val = eval(val_expr, env, defs)?;
            TLC_STATE.with(|state| {
                state.borrow_mut().insert(idx, val);
            });
            Ok(Value::Bool(true))
        }

        Expr::Any => Err(EvalError::domain_error(
            "Any cannot be evaluated directly, only used in membership tests",
        )),

        Expr::TLCEval(val) => eval(val, env, defs),

        Expr::IsABag(bag_expr) => {
            let v = eval(bag_expr, env, defs)?;
            if let Some(f) = v.as_function_map() {
                for count in f.values() {
                    if let Value::Int(n) = count {
                        if *n < 1 {
                            return Ok(Value::Bool(false));
                        }
                    } else {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            } else {
                Ok(Value::Bool(false))
            }
        }

        Expr::BagToSet(bag_expr) => {
            let f = eval_fn(bag_expr, env, defs)?;
            let dom: BTreeSet<Value> = f.keys().cloned().collect();
            Ok(Value::set(dom))
        }

        Expr::SetToBag(set_expr) => {
            let s = eval_set(set_expr, env, defs)?;
            let mut bag = BTreeMap::new();
            for elem in s {
                bag.insert(elem, Value::Int(1));
            }
            Ok(Value::func(bag))
        }

        Expr::BagIn(elem_expr, bag_expr) => {
            let elem = eval(elem_expr, env, defs)?;
            let bag = eval_fn(bag_expr, env, defs)?;
            if let Some(Value::Int(count)) = bag.get(&elem) {
                Ok(Value::Bool(*count >= 1))
            } else {
                Ok(Value::Bool(false))
            }
        }

        Expr::EmptyBag => Ok(Value::func(BTreeMap::new())),

        Expr::BagAdd(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            let mut result = b1.clone();
            for (elem, count) in b2 {
                let c2 = if let Value::Int(n) = count { n } else { 0 };
                let c1 = result
                    .get(&elem)
                    .and_then(|v| {
                        if let Value::Int(n) = v {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .unwrap_or(0);
                result.insert(elem, Value::Int(c1 + c2));
            }
            Ok(Value::func(result))
        }

        Expr::BagSub(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            let mut result = BTreeMap::new();
            for (elem, count) in &b1 {
                let c1 = if let Value::Int(n) = count { *n } else { 0 };
                let c2 = b2
                    .get(elem)
                    .and_then(|v| {
                        if let Value::Int(n) = v {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .unwrap_or(0);
                let diff = c1 - c2;
                if diff > 0 {
                    result.insert(elem.clone(), Value::Int(diff));
                }
            }
            Ok(Value::func(result))
        }

        Expr::BagUnion(bags_expr) => {
            let bags_set = eval_set(bags_expr, env, defs)?;
            let mut result: BTreeMap<Value, Value> = BTreeMap::new();
            for bag_val in bags_set {
                if let Some(bag) = bag_val.as_function_map() {
                    for (elem, count) in bag {
                        let c_new = if let Value::Int(n) = count { n } else { 0 };
                        let c_old = result
                            .get(&elem)
                            .and_then(|v| {
                                if let Value::Int(n) = v {
                                    Some(*n)
                                } else {
                                    None
                                }
                            })
                            .unwrap_or(0);
                        result.insert(elem, Value::Int(c_old + c_new));
                    }
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Bag (Fn)",
                        got: bag_val,
                        context: Some("BagUnion element"),
                        span: None,
                    });
                }
            }
            Ok(Value::func(result))
        }

        Expr::SqSubseteq(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            for (elem, count) in &b1 {
                let c1 = if let Value::Int(n) = count { *n } else { 0 };
                let c2 = b2
                    .get(elem)
                    .and_then(|v| {
                        if let Value::Int(n) = v {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .unwrap_or(0);
                if c1 > c2 {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::SubBag(bag_expr) => {
            let bag = eval_fn(bag_expr, env, defs)?;
            let elements: Vec<(Value, i64)> = bag
                .iter()
                .filter_map(|(elem, count)| {
                    if let Value::Int(n) = count {
                        Some((elem.clone(), *n))
                    } else {
                        None
                    }
                })
                .collect();
            if elements.iter().map(|(_, c)| *c).sum::<i64>() > 20 {
                return Err(EvalError::domain_error(
                    "SubBag of bag with more than 20 total copies is too large",
                ));
            }
            let mut result_set = BTreeSet::new();
            enumerate_subbags(&elements, 0, BTreeMap::new(), &mut result_set);
            Ok(Value::set(result_set))
        }

        Expr::BagOfAll(expr, bag_expr) => {
            let bag = eval_fn(bag_expr, env, defs)?;
            let mut result: BTreeMap<Value, Value> = BTreeMap::new();
            if let Expr::Lambda(params, body) = expr.as_ref() {
                if params.len() != 1 {
                    return Err(EvalError::domain_error(
                        "BagOfAll expects a single-argument lambda",
                    ));
                }
                let prev = env.remove(&params[0]);
                for (elem, count) in bag {
                    let c = if let Value::Int(n) = count { n } else { 0 };
                    env.insert(params[0].clone(), elem);
                    let mapped = eval(body, env, defs)?;
                    let prev_count = result
                        .get(&mapped)
                        .and_then(|v| {
                            if let Value::Int(n) = v {
                                Some(*n)
                            } else {
                                None
                            }
                        })
                        .unwrap_or(0);
                    result.insert(mapped, Value::Int(prev_count + c));
                }
                match prev {
                    Some(old) => {
                        env.insert(params[0].clone(), old);
                    }
                    None => {
                        env.remove(&params[0]);
                    }
                }
            } else {
                return Err(EvalError::domain_error(
                    "BagOfAll requires a LAMBDA expression",
                ));
            }
            Ok(Value::func(result))
        }

        Expr::BagCardinality(bag_expr) => {
            let bag = eval_fn(bag_expr, env, defs)?;
            let mut total = 0i64;
            for count in bag.values() {
                if let Value::Int(n) = count {
                    total += n;
                }
            }
            Ok(Value::Int(total))
        }

        Expr::CopiesIn(elem_expr, bag_expr) => {
            let elem = eval(elem_expr, env, defs)?;
            let bag = eval_fn(bag_expr, env, defs)?;
            if let Some(Value::Int(count)) = bag.get(&elem) {
                Ok(Value::Int(*count))
            } else {
                Ok(Value::Int(0))
            }
        }

        Expr::If(cond, then_br, else_br) => {
            if eval_bool(cond, env, defs)? {
                eval(then_br, env, defs)
            } else {
                eval(else_br, env, defs)
            }
        }

        Expr::Let(var, binding, body) => {
            if let Expr::FnDef(param, domain_expr, fn_body) = binding.as_ref() {
                let mut local_defs = defs.clone();
                local_defs.insert(var.clone(), (vec![], (**binding).clone()));
                let dom = eval_set(domain_expr, env, &local_defs)?;
                let dom_vec: Vec<_> = dom.into_iter().collect();
                let fn_result =
                    eval_fn_def_recursive(var, param, &dom_vec, fn_body, env, &local_defs)?;
                let prev = env.insert(var.clone(), Value::func(fn_result));
                let result = eval(body, env, &local_defs);
                match prev {
                    Some(old) => {
                        env.insert(var.clone(), old);
                    }
                    None => {
                        env.remove(var);
                    }
                }
                result
            } else {
                let val = eval(binding, env, defs)?;
                let prev = env.insert(var.clone(), val);
                let result = eval(body, env, defs);
                match prev {
                    Some(old) => {
                        env.insert(var.clone(), old);
                    }
                    None => {
                        env.remove(var);
                    }
                }
                result
            }
        }

        Expr::Case(branches) => {
            for (cond, result) in branches {
                if eval_bool(cond, env, defs)? {
                    return eval(result, env, defs);
                }
            }
            Err(EvalError::domain_error("no case matched"))
        }

        Expr::Unchanged(vars) => {
            let expanded = expand_unchanged_vars(vars, defs);
            for var in &expanded {
                let current = env
                    .get(var)
                    .ok_or_else(|| EvalError::undefined_var_with_env(var.clone(), env, defs))?;
                let primed = crate::intern::primed_name(var);
                let next = env
                    .get(&primed)
                    .ok_or_else(|| EvalError::undefined_var_with_env(primed, env, defs))?;
                if current != next {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::Always(_) => Err(EvalError::domain_error(
            "temporal operator [] (always) reached eval — it should be part of a spec body resolved via cfg SPECIFICATION, not evaluated as a state expression. Use INVARIANT for state-only safety properties.",
        )),

        Expr::Eventually(_) => Err(EvalError::domain_error(
            "temporal operator <> (eventually) reached eval — wrap it in a definition and reference it via cfg PROPERTY (with --check-liveness), don't use it as a state predicate.",
        )),

        Expr::LeadsTo(_, _) => Err(EvalError::domain_error(
            "temporal operator ~> (leads-to) reached eval — wrap it in a definition and reference it via cfg PROPERTY (with --check-liveness), don't use it as a state predicate.",
        )),

        Expr::WeakFairness(_, _) => Err(EvalError::domain_error(
            "temporal operator WF_vars (weak fairness) reached eval — it should be inside the spec body (e.g., `Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)`) referenced by cfg SPECIFICATION, where it is auto-extracted into fairness constraints. WF_vars cannot be used as a state predicate or invariant.",
        )),

        Expr::StrongFairness(_, _) => Err(EvalError::domain_error(
            "temporal operator SF_vars (strong fairness) reached eval — it should be inside the spec body referenced by cfg SPECIFICATION, where it is auto-extracted into fairness constraints. SF_vars cannot be used as a state predicate or invariant.",
        )),

        Expr::BoxAction(_, _) => Err(EvalError::domain_error(
            "temporal operator [A]_v (box action) reached eval — it should be inside the spec body referenced by cfg SPECIFICATION. Cannot be used as a state predicate.",
        )),

        Expr::DiamondAction(_, _) => Err(EvalError::domain_error(
            "temporal operator <<A>>_v (diamond action) reached eval — it should be inside the spec body referenced by cfg SPECIFICATION. Cannot be used as a state predicate.",
        )),

        Expr::EnabledOp(_) => Err(EvalError::domain_error(
            "ENABLED operator cannot be evaluated in explicit-state model checking",
        )),

        Expr::QualifiedCall(instance_expr, op, args) => match instance_expr.as_ref() {
            Expr::Var(instance_name) => RESOLVED_INSTANCES.with(|inst_ref| {
                let instances = inst_ref.borrow();
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

                let mut merged_defs = defs.clone();
                for (name, def) in instance_defs {
                    merged_defs.insert(name.clone(), def.clone());
                }

                let mut arg_vals = Vec::with_capacity(args.len());
                for arg_expr in args {
                    arg_vals.push(eval(arg_expr, env, defs)?);
                }
                let mut prevs = Vec::with_capacity(params.len());
                for (param, val) in params.iter().zip(arg_vals) {
                    prevs.push((param.clone(), env.insert(param.clone(), val)));
                }
                let result = eval(body, env, &merged_defs);
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
            }),
            Expr::FnCall(instance_name, instance_args) => {
                PARAMETERIZED_INSTANCES.with(|inst_ref| {
                    let instances = inst_ref.borrow();
                    let param_inst = instances.get(instance_name).ok_or_else(|| {
                        EvalError::domain_error(format!(
                            "parameterized instance {} not found",
                            instance_name
                        ))
                    })?;

                    if instance_args.len() != param_inst.params.len() {
                        return Err(EvalError::domain_error(format!(
                            "parameterized instance {} expects {} args, got {}",
                            instance_name,
                            param_inst.params.len(),
                            instance_args.len()
                        )));
                    }

                    let mut inst_arg_vals = Vec::with_capacity(instance_args.len());
                    for arg_expr in instance_args {
                        inst_arg_vals.push(eval(arg_expr, env, defs)?);
                    }

                    let instance_defs =
                        super::resolve_parameterized_defs(param_inst, inst_arg_vals);

                    let (params, body) = instance_defs.get(op).ok_or_else(|| {
                        EvalError::domain_error(format!(
                            "operator {} not found in instance {}",
                            op, instance_name
                        ))
                    })?;

                    if args.len() != params.len() {
                        return Err(EvalError::domain_error(format!(
                            "{}(...)!{} expects {} args, got {}",
                            instance_name,
                            op,
                            params.len(),
                            args.len()
                        )));
                    }

                    let mut merged_defs = defs.clone();
                    for (name, def) in &instance_defs {
                        merged_defs.insert(name.clone(), def.clone());
                    }

                    let mut arg_vals = Vec::with_capacity(args.len());
                    for arg_expr in args {
                        arg_vals.push(eval(arg_expr, env, defs)?);
                    }
                    let mut prevs = Vec::with_capacity(params.len());
                    for (param, val) in params.iter().zip(arg_vals) {
                        prevs.push((param.clone(), env.insert(param.clone(), val)));
                    }
                    let result = eval(body, env, &merged_defs);
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
                })
            }
            _ => Err(EvalError::domain_error(format!(
                "qualified call requires instance name or parameterized instance call, got {:?}",
                instance_expr
            ))),
        },

        Expr::LabeledAction(_label, action) => eval(action, env, defs),
    }
}

fn try_eval_unbounded_choose(
    var: &Arc<str>,
    body: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<Option<Value>> {
    use super::ast_utils::{expr_is_var, expr_references};
    match body {
        Expr::NotIn(lhs, set_expr) if expr_is_var(lhs, var) => {
            let excluded = eval_set(set_expr, env, defs)?;
            for i in 0..10_000 {
                let candidate = Value::Str(format!("MODEL_VALUE_{}", i).into());
                if !excluded.contains(&candidate) {
                    return Ok(Some(candidate));
                }
            }
            Ok(None)
        }
        Expr::Eq(lhs, rhs) if expr_is_var(lhs, var) && !expr_references(rhs, var) => {
            Ok(Some(eval(rhs, env, defs)?))
        }
        Expr::Eq(lhs, rhs) if expr_is_var(rhs, var) && !expr_references(lhs, var) => {
            Ok(Some(eval(lhs, env, defs)?))
        }
        _ => Ok(None),
    }
}
