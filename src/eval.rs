use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::ast::{Env, Expr, State, Value};
use crate::checker::format_value;
use crate::diagnostic::find_similar;

pub type Definitions = BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>;
pub type ResolvedInstances = BTreeMap<Arc<str>, Definitions>;

#[derive(Clone)]
pub struct EvalContext {
    pub state_vars: Vec<Arc<str>>,
    pub constants: Env,
    pub current_state: State,
}

thread_local! {
    static RNG: RefCell<fastrand::Rng> = RefCell::new(fastrand::Rng::with_seed(0));
    static TLC_STATE: RefCell<BTreeMap<i64, Value>> = const { RefCell::new(BTreeMap::new()) };
    static CHECKER_STATS: RefCell<CheckerStats> = const { RefCell::new(CheckerStats::new()) };
    static RESOLVED_INSTANCES: RefCell<ResolvedInstances> = const { RefCell::new(BTreeMap::new()) };
}

#[derive(Debug, Clone, Default)]
pub struct CheckerStats {
    pub distinct: i64,
    pub level: i64,
    pub diameter: i64,
    pub queue: i64,
    pub duration: i64,
    pub generated: i64,
}

impl CheckerStats {
    pub const fn new() -> Self {
        Self {
            distinct: 0,
            level: 0,
            diameter: 0,
            queue: 0,
            duration: 0,
            generated: 0,
        }
    }
}

pub fn set_random_seed(seed: u64) {
    RNG.with(|rng| *rng.borrow_mut() = fastrand::Rng::with_seed(seed));
}

pub fn reset_tlc_state() {
    TLC_STATE.with(|state| state.borrow_mut().clear());
}

pub fn update_checker_stats(stats: CheckerStats) {
    CHECKER_STATS.with(|s| *s.borrow_mut() = stats);
}

pub fn set_checker_level(level: i64) {
    CHECKER_STATS.with(|s| s.borrow_mut().level = level);
}

pub fn set_resolved_instances(instances: ResolvedInstances) {
    RESOLVED_INSTANCES.with(|inst| *inst.borrow_mut() = instances);
}

pub fn clear_resolved_instances() {
    RESOLVED_INSTANCES.with(|inst| inst.borrow_mut().clear());
}

#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVar { name: Arc<str>, suggestion: Option<Arc<str>> },
    TypeMismatch { expected: &'static str, got: Value },
    DivisionByZero,
    EmptyChoose,
    DomainError(String),
}

impl EvalError {
    pub fn undefined_var(name: Arc<str>) -> Self {
        Self::UndefinedVar { name, suggestion: None }
    }

    pub fn undefined_var_with_env(name: Arc<str>, env: &Env, defs: &Definitions) -> Self {
        let candidates = env.keys().map(|s| s.as_ref())
            .chain(defs.keys().map(|s| s.as_ref()));
        let suggestion = find_similar(&name, candidates, 2).map(|s| s.into());
        Self::UndefinedVar { name, suggestion }
    }
}

type Result<T> = std::result::Result<T, EvalError>;

fn eval_fn_def_recursive(
    fn_name: &Arc<str>,
    param: &Arc<str>,
    domain: &[Value],
    body: &Expr,
    env: &Env,
    defs: &Definitions,
) -> Result<BTreeMap<Value, Value>> {
    let memo: RefCell<BTreeMap<Value, Value>> = RefCell::new(BTreeMap::new());

    for val in domain.iter() {
        if memo.borrow().contains_key(val) {
            continue;
        }
        let mut local = env.clone();
        local.insert(param.clone(), val.clone());
        let result = eval_with_memo(body, &local, defs, fn_name, param, domain, &memo)?;
        memo.borrow_mut().insert(val.clone(), result);
    }

    Ok(memo.into_inner())
}

#[allow(clippy::only_used_in_recursion)]
fn eval_with_memo(
    expr: &Expr,
    env: &Env,
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
                    let mut local = env.clone();
                    local.insert(p.clone(), av.clone());
                    let result =
                        eval_with_memo(body, &local, defs, fn_name, fn_param, fn_domain, memo)?;
                    memo.borrow_mut().insert(av, result.clone());
                    return Ok(result);
                }
            }
            let fval = eval_with_memo(f, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let av = eval_with_memo(arg, env, defs, fn_name, fn_param, fn_domain, memo)?;
            match fval {
                Value::Fn(fv) => fv
                    .get(&av)
                    .cloned()
                    .ok_or_else(|| EvalError::DomainError("key not in function domain".into())),
                _ => Err(EvalError::TypeMismatch { expected: "Fn", got: fval }),
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
                Value::Bool(true) => eval_with_memo(then_br, env, defs, fn_name, fn_param, fn_domain, memo),
                Value::Bool(false) => eval_with_memo(else_br, env, defs, fn_name, fn_param, fn_domain, memo),
                _ => Err(EvalError::TypeMismatch { expected: "Bool", got: cv }),
            }
        }

        Expr::Add(l, r) => {
            let lv = eval_with_memo(l, env, defs, fn_name, fn_param, fn_domain, memo)?;
            let rv = eval_with_memo(r, env, defs, fn_name, fn_param, fn_domain, memo)?;
            match (lv, rv) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
                (a, b) => Err(EvalError::DomainError(format!("cannot add {:?} and {:?}", a, b))),
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
                (Value::Set(a), Value::Set(b)) => Ok(Value::Set(a.difference(&b).cloned().collect())),
                (a, b) => Err(EvalError::DomainError(format!("set minus on {:?} and {:?}", a, b))),
            }
        }

        Expr::SetEnum(elems) => {
            let mut result = BTreeSet::new();
            for e in elems {
                result.insert(eval_with_memo(e, env, defs, fn_name, fn_param, fn_domain, memo)?);
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
            Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
        }

        Expr::Prime(name) => {
            let primed: Arc<str> = format!("{}'", name).into();
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
            if matches!(set.as_ref(), Expr::Any) {
                return Ok(Value::Bool(true));
            }
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
            if matches!(set.as_ref(), Expr::Any) {
                return Ok(Value::Bool(false));
            }
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
                            && t1.len() == 2 && t2.len() == 2 && t1[1] == t2[0]
                        {
                            let new_pair = Value::Tuple(vec![t1[0].clone(), t2[1].clone()]);
                            if !result.contains(&new_pair) {
                                result.insert(new_pair);
                                changed = true;
                            }
                        }
                    }
                }
            }
            Ok(Value::Set(result))
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
                            && t1.len() == 2 && t2.len() == 2 && t1[1] == t2[0]
                        {
                            let new_pair = Value::Tuple(vec![t1[0].clone(), t2[1].clone()]);
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
                    result.insert(Value::Tuple(vec![t[0].clone(), t[0].clone()]));
                    result.insert(Value::Tuple(vec![t[1].clone(), t[1].clone()]));
                }
            }
            Ok(Value::Set(result))
        }

        Expr::ActionCompose(_, _) => Err(EvalError::DomainError(
            "action composition (\\cdot) cannot be evaluated in explicit-state model checking".into()
        )),

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
            let mut scoped_env = env.clone();
            for val in domain_vals {
                scoped_env.insert(var.clone(), val.clone());
                if eval_bool(predicate, &scoped_env, defs)? {
                    result.insert(val);
                }
            }
            Ok(Value::Set(result))
        }

        Expr::SetMap(var, domain, body) => {
            let domain_vals = eval_set(domain, env, defs)?;
            let mut result = BTreeSet::new();
            let mut scoped_env = env.clone();
            for val in domain_vals {
                scoped_env.insert(var.clone(), val);
                result.insert(eval(body, &scoped_env, defs)?);
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
            let mut scoped_env = env.clone();
            for val in dom {
                scoped_env.insert(var.clone(), val);
                if eval_bool(body, &scoped_env, defs)? {
                    return Ok(Value::Bool(true));
                }
            }
            Ok(Value::Bool(false))
        }

        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let mut scoped_env = env.clone();
            for val in dom {
                scoped_env.insert(var.clone(), val);
                if !eval_bool(body, &scoped_env, defs)? {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::Choose(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let mut scoped_env = env.clone();
            for val in &dom {
                scoped_env.insert(var.clone(), val.clone());
                if eval_bool(body, &scoped_env, defs)? {
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
            let dom_vec: Vec<_> = dom.into_iter().collect();
            let placeholder_name: Arc<str> = "".into();
            let result = eval_fn_def_recursive(&placeholder_name, var, &dom_vec, body, env, defs)?;
            Ok(Value::Fn(result))
        }

        Expr::FnCall(name, args) => {
            match name.as_ref() {
                "BitAnd" => {
                    if args.len() != 2 {
                        return Err(EvalError::DomainError(format!(
                            "BitAnd expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a & b));
                }
                "BitOr" => {
                    if args.len() != 2 {
                        return Err(EvalError::DomainError(format!(
                            "BitOr expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a | b));
                }
                "BitXor" => {
                    if args.len() != 2 {
                        return Err(EvalError::DomainError(format!(
                            "BitXor expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a ^ b));
                }
                "BitNot" => {
                    if args.len() != 1 {
                        return Err(EvalError::DomainError(format!(
                            "BitNot expects 1 arg, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    return Ok(Value::Int(!a));
                }
                "ShiftLeft" | "LeftShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::DomainError(format!(
                            "{} expects 2 args, got {}", name, args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::DomainError(format!(
                            "shift amount {} out of range (0-63)", b
                        )));
                    }
                    return Ok(Value::Int(a << b));
                }
                "ShiftRight" | "RightShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::DomainError(format!(
                            "{} expects 2 args, got {}", name, args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::DomainError(format!(
                            "shift amount {} out of range (0-63)", b
                        )));
                    }
                    return Ok(Value::Int(a >> b));
                }
                _ => {}
            }
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
                Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
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
            let v = eval(tup, env, defs)?;
            match v {
                Value::Tuple(tv) => tv
                    .get(*idx)
                    .cloned()
                    .ok_or_else(|| EvalError::DomainError(format!("index {} out of bounds", idx))),
                Value::Fn(fv) => {
                    let key = Value::Int((*idx + 1) as i64);
                    fv.get(&key)
                        .cloned()
                        .ok_or_else(|| EvalError::DomainError("key not in function domain".into()))
                }
                other => Err(EvalError::TypeMismatch {
                    expected: "Tuple or Fn",
                    got: other,
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
                return Err(EvalError::DomainError(format!(
                    "Permutations of set with {} elements is too large (max 10)",
                    n
                )));
            }
            let perms = permutations(&elements);
            let result: BTreeSet<Value> = perms.into_iter().map(Value::Tuple).collect();
            Ok(Value::Set(result))
        }

        Expr::SortSeq(seq_expr, cmp_expr) => {
            let tv = eval_tuple(seq_expr, env, defs)?;
            let mut result = tv;
            if let Expr::Lambda(params, body) = cmp_expr.as_ref() {
                if params.len() != 2 {
                    return Err(EvalError::DomainError(
                        "SortSeq comparator must take exactly 2 arguments".into(),
                    ));
                }
                let param_a = &params[0];
                let param_b = &params[1];
                result.sort_by(|a, b| {
                    let mut local = env.clone();
                    local.insert(param_a.clone(), a.clone());
                    local.insert(param_b.clone(), b.clone());
                    match eval_bool(body, &local, defs) {
                        Ok(true) => std::cmp::Ordering::Less,
                        Ok(false) => std::cmp::Ordering::Greater,
                        Err(_) => std::cmp::Ordering::Equal,
                    }
                });
            } else {
                return Err(EvalError::DomainError(
                    "SortSeq comparator must be a LAMBDA expression".into(),
                ));
            }
            Ok(Value::Tuple(result))
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
                return Err(EvalError::DomainError("RandomElement of empty set".into()));
            }
            let elements: Vec<_> = set.into_iter().collect();
            let idx = RNG.with(|rng| rng.borrow_mut().usize(..elements.len()));
            Ok(elements.into_iter().nth(idx).unwrap())
        }

        Expr::TLCGet(idx_expr) => {
            let key = eval(idx_expr, env, defs)?;
            match key {
                Value::Int(idx) => TLC_STATE.with(|state| {
                    Ok(state.borrow().get(&idx).cloned().unwrap_or(Value::Bool(false)))
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
                        other => Err(EvalError::DomainError(format!(
                            "TLCGet: unknown key \"{}\"", other
                        ))),
                    }
                }),
                other => Err(EvalError::TypeMismatch {
                    expected: "Int or Str",
                    got: other,
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

        Expr::Any => Err(EvalError::DomainError(
            "Any cannot be evaluated directly, only used in membership tests".into(),
        )),

        Expr::TLCEval(val) => eval(val, env, defs),

        Expr::IsABag(bag_expr) => {
            let v = eval(bag_expr, env, defs)?;
            if let Value::Fn(f) = v {
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
            Ok(Value::Set(dom))
        }

        Expr::SetToBag(set_expr) => {
            let s = eval_set(set_expr, env, defs)?;
            let mut bag = BTreeMap::new();
            for elem in s {
                bag.insert(elem, Value::Int(1));
            }
            Ok(Value::Fn(bag))
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

        Expr::EmptyBag => Ok(Value::Fn(BTreeMap::new())),

        Expr::BagAdd(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            let mut result = b1.clone();
            for (elem, count) in b2 {
                let c2 = if let Value::Int(n) = count { n } else { 0 };
                let c1 = result.get(&elem)
                    .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                    .unwrap_or(0);
                result.insert(elem, Value::Int(c1 + c2));
            }
            Ok(Value::Fn(result))
        }

        Expr::BagSub(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            let mut result = BTreeMap::new();
            for (elem, count) in &b1 {
                let c1 = if let Value::Int(n) = count { *n } else { 0 };
                let c2 = b2.get(elem)
                    .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                    .unwrap_or(0);
                let diff = c1 - c2;
                if diff > 0 {
                    result.insert(elem.clone(), Value::Int(diff));
                }
            }
            Ok(Value::Fn(result))
        }

        Expr::BagUnion(bags_expr) => {
            let bags_set = eval_set(bags_expr, env, defs)?;
            let mut result: BTreeMap<Value, Value> = BTreeMap::new();
            for bag_val in bags_set {
                if let Value::Fn(bag) = bag_val {
                    for (elem, count) in bag {
                        let c_new = if let Value::Int(n) = count { n } else { 0 };
                        let c_old = result.get(&elem)
                            .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                            .unwrap_or(0);
                        result.insert(elem, Value::Int(c_old + c_new));
                    }
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Bag (Fn)",
                        got: bag_val,
                    });
                }
            }
            Ok(Value::Fn(result))
        }

        Expr::SqSubseteq(left, right) => {
            let b1 = eval_fn(left, env, defs)?;
            let b2 = eval_fn(right, env, defs)?;
            for (elem, count) in &b1 {
                let c1 = if let Value::Int(n) = count { *n } else { 0 };
                let c2 = b2.get(elem)
                    .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                    .unwrap_or(0);
                if c1 > c2 {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::SubBag(bag_expr) => {
            let bag = eval_fn(bag_expr, env, defs)?;
            let elements: Vec<(Value, i64)> = bag.iter()
                .filter_map(|(elem, count)| {
                    if let Value::Int(n) = count {
                        Some((elem.clone(), *n))
                    } else {
                        None
                    }
                })
                .collect();
            if elements.iter().map(|(_, c)| *c).sum::<i64>() > 20 {
                return Err(EvalError::DomainError(
                    "SubBag of bag with more than 20 total copies is too large".into()
                ));
            }
            let mut result_set = BTreeSet::new();
            enumerate_subbags(&elements, 0, BTreeMap::new(), &mut result_set);
            Ok(Value::Set(result_set))
        }

        Expr::BagOfAll(expr, bag_expr) => {
            let bag = eval_fn(bag_expr, env, defs)?;
            let mut result: BTreeMap<Value, Value> = BTreeMap::new();
            if let Expr::Lambda(params, body) = expr.as_ref() {
                if params.len() != 1 {
                    return Err(EvalError::DomainError(
                        "BagOfAll expects a single-argument lambda".into()
                    ));
                }
                for (elem, count) in bag {
                    let c = if let Value::Int(n) = count { n } else { 0 };
                    let mut local = env.clone();
                    local.insert(params[0].clone(), elem);
                    let mapped = eval(body, &local, defs)?;
                    let prev = result.get(&mapped)
                        .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                        .unwrap_or(0);
                    result.insert(mapped, Value::Int(prev + c));
                }
            } else {
                return Err(EvalError::DomainError(
                    "BagOfAll requires a LAMBDA expression".into()
                ));
            }
            Ok(Value::Fn(result))
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
                let fn_result = eval_fn_def_recursive(var, param, &dom_vec, fn_body, env, &local_defs)?;
                let mut local = env.clone();
                local.insert(var.clone(), Value::Fn(fn_result));
                eval(body, &local, &local_defs)
            } else {
                let val = eval(binding, env, defs)?;
                let mut local = env.clone();
                local.insert(var.clone(), val);
                eval(body, &local, defs)
            }
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
                    .ok_or_else(|| EvalError::undefined_var_with_env(var.clone(), env, defs))?;
                let primed: Arc<str> = format!("{}'", var).into();
                let next = env.get(&primed).ok_or_else(|| EvalError::undefined_var_with_env(primed, env, defs))?;
                if current != next {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }

        Expr::Always(_) => Err(EvalError::DomainError(
            "temporal operator [] (always) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::Eventually(_) => Err(EvalError::DomainError(
            "temporal operator <> (eventually) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::LeadsTo(_, _) => Err(EvalError::DomainError(
            "temporal operator ~> (leads-to) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::WeakFairness(_, _) => Err(EvalError::DomainError(
            "temporal operator WF (weak fairness) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::StrongFairness(_, _) => Err(EvalError::DomainError(
            "temporal operator SF (strong fairness) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::BoxAction(_, _) => Err(EvalError::DomainError(
            "temporal operator [A]_v (box action) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::DiamondAction(_, _) => Err(EvalError::DomainError(
            "temporal operator <<A>>_v (diamond action) cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::EnabledOp(_) => Err(EvalError::DomainError(
            "ENABLED operator cannot be evaluated in explicit-state model checking".into()
        )),

        Expr::QualifiedCall(instance, op, args) => {
            RESOLVED_INSTANCES.with(|inst_ref| {
                let instances = inst_ref.borrow();
                if instances.is_empty() {
                    return Err(EvalError::DomainError(format!(
                        "qualified call {}!{} requires resolved instances",
                        instance, op
                    )));
                }

                let instance_defs = instances
                    .get(instance)
                    .ok_or_else(|| EvalError::DomainError(format!("instance {} not found", instance)))?;

                let (params, body) = instance_defs
                    .get(op)
                    .ok_or_else(|| EvalError::DomainError(format!(
                        "operator {} not found in instance {}",
                        op, instance
                    )))?;

                if args.len() != params.len() {
                    return Err(EvalError::DomainError(format!(
                        "{}!{} expects {} args, got {}",
                        instance, op, params.len(), args.len()
                    )));
                }

                let mut local = env.clone();
                for (param, arg_expr) in params.iter().zip(args) {
                    let arg_val = eval(arg_expr, env, defs)?;
                    local.insert(param.clone(), arg_val);
                }

                eval(body, &local, defs)
            })
        }

        Expr::LabeledAction(_label, action) => {
            eval(action, env, defs)
        }
    }
}

pub fn eval_with_instances(
    expr: &Expr,
    env: &Env,
    defs: &Definitions,
    instances: &ResolvedInstances,
) -> Result<Value> {
    match expr {
        Expr::QualifiedCall(instance, op, args) => {
            let instance_defs = instances
                .get(instance)
                .ok_or_else(|| EvalError::DomainError(format!("instance {} not found", instance)))?;

            let (params, body) = instance_defs
                .get(op)
                .ok_or_else(|| EvalError::DomainError(format!(
                    "operator {} not found in instance {}",
                    op, instance
                )))?;

            if args.len() != params.len() {
                return Err(EvalError::DomainError(format!(
                    "{}!{} expects {} args, got {}",
                    instance, op, params.len(), args.len()
                )));
            }

            let mut local = env.clone();
            for (param, arg_expr) in params.iter().zip(args) {
                let arg_val = eval_with_instances(arg_expr, env, defs, instances)?;
                local.insert(param.clone(), arg_val);
            }

            eval_with_instances(body, &local, defs, instances)
        }
        _ => eval(expr, env, defs),
    }
}

pub fn eval_with_context(
    expr: &Expr,
    env: &Env,
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
                    return Err(EvalError::DomainError(format!(
                        "function {} expects {} args, got {}",
                        name,
                        params.len(),
                        args.len()
                    )));
                }
                let mut local = env.clone();
                for (param, arg_expr) in params.iter().zip(args) {
                    let arg_val = eval_with_context(arg_expr, env, defs, ctx)?;
                    local.insert(param.clone(), arg_val);
                }
                eval_with_context(body, &local, defs, ctx)
            } else {
                Err(EvalError::undefined_var_with_env(name.clone(), env, defs))
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
            let mut scoped_env = env.clone();
            for val in dom {
                scoped_env.insert(var.clone(), val);
                if !eval_bool_with_context(body, &scoped_env, defs, ctx)? {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let mut scoped_env = env.clone();
            for val in dom {
                scoped_env.insert(var.clone(), val);
                if eval_bool_with_context(body, &scoped_env, defs, ctx)? {
                    return Ok(Value::Bool(true));
                }
            }
            Ok(Value::Bool(false))
        }
        _ => eval(expr, env, defs),
    }
}

fn eval_bool_with_context(expr: &Expr, env: &Env, defs: &Definitions, ctx: &EvalContext) -> Result<bool> {
    match eval_with_context(expr, env, defs, ctx)? {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: other,
        }),
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
    let mut base_env = state_to_env(current);
    for (k, v) in constants {
        base_env.insert(k.clone(), v.clone());
    }

    if let Expr::Or(_, _) = next {
        let disjuncts = collect_disjuncts(next);
        let mut all_results = indexmap::IndexSet::new();
        for disjunct in &disjuncts {
            if let Expr::Exists(_, _, _) = disjunct {
                let expanded_envs = expand_exists_disjuncts(disjunct, &base_env, defs)?;
                let action_body = get_action_body(disjunct);
                for action_env in expanded_envs {
                    let mut results = Vec::new();
                    enumerate_next(action_body, &action_env, vars, 0, defs, &mut results)?;
                    for state in results {
                        all_results.insert(state);
                    }
                }
            } else {
                let mut results = Vec::new();
                enumerate_next(disjunct, &base_env, vars, 0, defs, &mut results)?;
                for state in results {
                    all_results.insert(state);
                }
            }
        }
        return Ok(all_results.into_iter().collect());
    }

    let mut results = Vec::new();
    enumerate_next(next, &base_env, vars, 0, defs, &mut results)?;
    Ok(results)
}

fn collect_disjuncts(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::Or(l, r) => {
            let mut result = collect_disjuncts(l);
            result.extend(collect_disjuncts(r));
            result
        }
        _ => vec![expr],
    }
}

fn expand_exists_disjuncts(expr: &Expr, env: &Env, defs: &Definitions) -> Result<Vec<Env>> {
    match expr {
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let mut all_envs = Vec::new();
            for val in dom {
                let mut new_env = env.clone();
                new_env.insert(var.clone(), val);
                let nested_envs = expand_exists_disjuncts(body, &new_env, defs)?;
                all_envs.extend(nested_envs);
            }
            Ok(all_envs)
        }
        _ => Ok(vec![env.clone()]),
    }
}

fn get_action_body(expr: &Expr) -> &Expr {
    match expr {
        Expr::Exists(_, _, body) => get_action_body(body),
        _ => expr,
    }
}

pub fn is_action_enabled(
    action: &Expr,
    current: &State,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<bool> {
    let mut base_env = state_to_env(current);
    for (k, v) in constants {
        base_env.insert(k.clone(), v.clone());
    }
    check_enabled(action, &base_env, vars, 0, defs)
}

fn check_enabled(
    action: &Expr,
    env: &Env,
    vars: &[Arc<str>],
    var_idx: usize,
    defs: &Definitions,
) -> Result<bool> {
    if var_idx >= vars.len() {
        return eval_bool(action, env, defs);
    }

    let var = &vars[var_idx];
    let primed: Arc<str> = format!("{}'", var).into();
    let candidates = infer_candidates(action, env, var, defs)?;

    let mut scoped_env = env.clone();
    for candidate in candidates {
        scoped_env.insert(primed.clone(), candidate);
        if check_enabled(action, &scoped_env, vars, var_idx + 1, defs)? {
            return Ok(true);
        }
    }

    Ok(false)
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

    let mut scoped_env = env.clone();
    for candidate in candidates {
        scoped_env.insert(primed.clone(), candidate);
        enumerate_next(next, &scoped_env, vars, var_idx + 1, defs, results)?;
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
                let mut scoped_env = env.clone();
                for val in dom {
                    scoped_env.insert(bound.clone(), val);
                    collect_candidates(body, &scoped_env, var, defs, candidates)?;
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

        Expr::FnCall(name, args) => {
            if let Some((params, body)) = defs.get(name)
                && params.len() == args.len()
            {
                let mut local = env.clone();
                for (param, arg) in params.iter().zip(args.iter()) {
                    if let Ok(val) = eval(arg, env, defs) {
                        local.insert(param.clone(), val);
                    }
                }
                collect_candidates(body, &local, var, defs, candidates)?;
            }
        }

        Expr::LabeledAction(_, action) => {
            collect_candidates(action, env, var, defs, candidates)?;
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

    let mut scoped_env = env.clone();
    for candidate in candidates {
        scoped_env.insert(var.clone(), candidate);
        enumerate_init(init, &scoped_env, vars, var_idx + 1, domains, defs, results)?;
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

fn enumerate_subbags(
    elements: &[(Value, i64)],
    idx: usize,
    current: BTreeMap<Value, Value>,
    results: &mut BTreeSet<Value>,
) {
    if idx >= elements.len() {
        results.insert(Value::Fn(current));
        return;
    }
    let (elem, max_count) = &elements[idx];
    for count in 0..=*max_count {
        let mut next = current.clone();
        if count > 0 {
            next.insert(elem.clone(), Value::Int(count));
        }
        enumerate_subbags(elements, idx + 1, next, results);
    }
}
