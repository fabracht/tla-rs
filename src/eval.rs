use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
#[cfg(feature = "profiling")]
use std::time::Instant;

use crate::ast::{Env, Expr, State, Value};
use crate::checker::format_value;
use crate::diagnostic::find_similar;
use crate::span::Span;

pub type Definitions = BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>;
pub type ResolvedInstances = BTreeMap<Arc<str>, Definitions>;

#[derive(Clone)]
pub struct EvalContext {
    pub state_vars: Vec<Arc<str>>,
    pub constants: Env,
    pub current_state: State,
}

#[cfg(feature = "profiling")]
#[derive(Debug, Clone, Default)]
pub struct ProfilingStats {
    pub eval_calls: u64,
    pub next_states_time_ns: u128,
    pub next_states_calls: u64,
    pub enumerate_next_time_ns: u128,
    pub enumerate_next_calls: u64,
    pub infer_candidates_time_ns: u128,
    pub infer_candidates_calls: u64,
    pub init_states_time_ns: u128,
    pub init_states_calls: u64,
}

#[cfg(feature = "profiling")]
impl ProfilingStats {
    pub const fn new() -> Self {
        Self {
            eval_calls: 0,
            next_states_time_ns: 0,
            next_states_calls: 0,
            enumerate_next_time_ns: 0,
            enumerate_next_calls: 0,
            infer_candidates_time_ns: 0,
            infer_candidates_calls: 0,
            init_states_time_ns: 0,
            init_states_calls: 0,
        }
    }
}

thread_local! {
    static RNG: RefCell<fastrand::Rng> = RefCell::new(fastrand::Rng::with_seed(0));
    static TLC_STATE: RefCell<BTreeMap<i64, Value>> = const { RefCell::new(BTreeMap::new()) };
    static CHECKER_STATS: RefCell<CheckerStats> = const { RefCell::new(CheckerStats::new()) };
    static RESOLVED_INSTANCES: RefCell<ResolvedInstances> = const { RefCell::new(BTreeMap::new()) };
    #[cfg(feature = "profiling")]
    static PROFILING_STATS: RefCell<ProfilingStats> = const { RefCell::new(ProfilingStats::new()) };
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

#[cfg(feature = "profiling")]
pub fn reset_profiling_stats() {
    PROFILING_STATS.with(|s| *s.borrow_mut() = ProfilingStats::new());
}

#[cfg(feature = "profiling")]
pub fn get_profiling_stats() -> ProfilingStats {
    PROFILING_STATS.with(|s| s.borrow().clone())
}

#[cfg(feature = "profiling")]
pub fn report_profiling_stats() {
    let stats = get_profiling_stats();
    let next_states_ms = stats.next_states_time_ns / 1_000_000;
    let enumerate_ms = stats.enumerate_next_time_ns / 1_000_000;
    let infer_ms = stats.infer_candidates_time_ns / 1_000_000;
    let init_ms = stats.init_states_time_ns / 1_000_000;

    eprintln!("=== Profiling Stats ===");
    eprintln!("eval:             {:>12} calls", stats.eval_calls);
    eprintln!("init_states:      {:>8}ms ({} calls, {:.2}µs/call)",
        init_ms, stats.init_states_calls,
        if stats.init_states_calls > 0 { stats.init_states_time_ns as f64 / stats.init_states_calls as f64 / 1000.0 } else { 0.0 });
    eprintln!("next_states:      {:>8}ms ({} calls, {:.2}µs/call)",
        next_states_ms, stats.next_states_calls,
        if stats.next_states_calls > 0 { stats.next_states_time_ns as f64 / stats.next_states_calls as f64 / 1000.0 } else { 0.0 });
    eprintln!("enumerate_next:   {:>8}ms ({} calls, {:.2}µs/call)",
        enumerate_ms, stats.enumerate_next_calls,
        if stats.enumerate_next_calls > 0 { stats.enumerate_next_time_ns as f64 / stats.enumerate_next_calls as f64 / 1000.0 } else { 0.0 });
    eprintln!("infer_candidates: {:>8}ms ({} calls, {:.2}µs/call)",
        infer_ms, stats.infer_candidates_calls,
        if stats.infer_candidates_calls > 0 { stats.infer_candidates_time_ns as f64 / stats.infer_candidates_calls as f64 / 1000.0 } else { 0.0 });
    eprintln!("=======================");
}

#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVar { name: Arc<str>, suggestion: Option<Arc<str>>, span: Option<Span> },
    TypeMismatch { expected: &'static str, got: Value, context: Option<&'static str>, span: Option<Span> },
    DivisionByZero { span: Option<Span> },
    EmptyChoose { span: Option<Span> },
    DomainError { message: String, span: Option<Span> },
}

impl EvalError {
    pub fn undefined_var(name: Arc<str>) -> Self {
        Self::UndefinedVar { name, suggestion: None, span: None }
    }

    pub fn undefined_var_with_env(name: Arc<str>, env: &Env, defs: &Definitions) -> Self {
        let candidates = env.keys().map(|s| s.as_ref())
            .chain(defs.keys().map(|s| s.as_ref()));
        let suggestion = find_similar(&name, candidates, 2).map(|s| s.into());
        Self::UndefinedVar { name, suggestion, span: None }
    }

    pub fn type_mismatch(expected: &'static str, got: Value) -> Self {
        Self::TypeMismatch { expected, got, context: None, span: None }
    }

    pub fn type_mismatch_ctx(expected: &'static str, got: Value, context: &'static str) -> Self {
        Self::TypeMismatch { expected, got, context: Some(context), span: None }
    }

    pub fn division_by_zero() -> Self {
        Self::DivisionByZero { span: None }
    }

    pub fn empty_choose() -> Self {
        Self::EmptyChoose { span: None }
    }

    pub fn domain_error(msg: impl Into<String>) -> Self {
        Self::DomainError { message: msg.into(), span: None }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        match &mut self {
            Self::UndefinedVar { span: s, .. } |
            Self::TypeMismatch { span: s, .. } |
            Self::DivisionByZero { span: s } |
            Self::EmptyChoose { span: s } |
            Self::DomainError { span: s, .. } => *s = Some(span),
        }
        self
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVar { span, .. } |
            Self::TypeMismatch { span, .. } |
            Self::DivisionByZero { span } |
            Self::EmptyChoose { span } |
            Self::DomainError { span, .. } => *span,
        }
    }
}

type Result<T> = std::result::Result<T, EvalError>;

fn value_type_name(val: &Value) -> &'static str {
    match val {
        Value::Bool(_) => "Bool",
        Value::Int(_) => "Int",
        Value::Str(_) => "Str",
        Value::Set(_) => "Set",
        Value::Fn(_) => "Function",
        Value::Record(_) => "Record",
        Value::Tuple(_) => "Sequence",
    }
}

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
                    .ok_or_else(|| EvalError::domain_error(format!(
                        "key {} not in function domain",
                        format_value(&av)
                    ))),
                Value::Tuple(tv) => {
                    if let Value::Int(idx) = av {
                        let i = idx as usize;
                        if i >= 1 && i <= tv.len() {
                            Ok(tv[i - 1].clone())
                        } else {
                            Err(EvalError::domain_error(format!(
                                "sequence index {} out of bounds (sequence has {} elements)",
                                idx, tv.len()
                            )))
                        }
                    } else {
                        Err(EvalError::TypeMismatch { expected: "Int", got: av, context: Some("sequence index"), span: None })
                    }
                }
                other => Err(EvalError::type_mismatch_ctx("Fn or Sequence", other, "function application")),
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
                (Value::Set(a), Value::Set(b)) => Ok(Value::Set(a.difference(&b).cloned().collect())),
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

        Expr::ActionCompose(_, _) => Err(EvalError::domain_error("action composition (\\cdot) cannot be evaluated in explicit-state model checking")),

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
            Ok(Value::Set(set))
        }

        Expr::SetRange(lo, hi) => {
            let l = eval_int(lo, env, defs)?;
            let h = eval_int(hi, env, defs)?;
            let set: BTreeSet<Value> = (l..=h).map(Value::Int).collect();
            Ok(Value::Set(set))
        }

        Expr::SetFilter(var, domain, predicate) => {
            if let Expr::Powerset(inner) = domain.as_ref()
                && let Some(constraint) = detect_cardinality_constraint(predicate, var, env, defs)
            {
                let base_set = eval_set(inner, env, defs)?;
                let elements: Vec<_> = base_set.into_iter().collect();
                return Ok(Value::Set(generate_subsets_with_constraint(&elements, constraint)));
            }

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
                    return Err(EvalError::TypeMismatch { expected: "Set", got: val, context: Some("UNION element"),  span: None });
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
            Err(EvalError::empty_choose())
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
                    .ok_or_else(|| EvalError::domain_error(format!(
                        "key {} not in function domain",
                        format_value(&av)
                    ))),
                Value::Tuple(tv) => {
                    if let Value::Int(idx) = av {
                        let i = idx as usize;
                        if i >= 1 && i <= tv.len() {
                            Ok(tv[i - 1].clone())
                        } else {
                            Err(EvalError::domain_error(format!(
                                "sequence index {} out of bounds (sequence has {} elements)",
                                idx, tv.len()
                            )))
                        }
                    } else {
                        Err(EvalError::TypeMismatch { expected: "Int", got: av, context: Some("sequence index"),  span: None })
                    }
                }
                other => Err(EvalError::TypeMismatch { expected: "Fn or Tuple", got: other, context: Some("function application"),  span: None }),
            }
        }

        Expr::Lambda(_params, _body) => {
            Err(EvalError::domain_error("lambda expression cannot be evaluated directly; must be applied"))
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
                        return Err(EvalError::domain_error(format!(
                            "BitAnd expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a & b));
                }
                "BitOr" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "BitOr expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a | b));
                }
                "BitXor" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "BitXor expects 2 args, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    return Ok(Value::Int(a ^ b));
                }
                "BitNot" => {
                    if args.len() != 1 {
                        return Err(EvalError::domain_error(format!(
                            "BitNot expects 1 arg, got {}", args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    return Ok(Value::Int(!a));
                }
                "ShiftLeft" | "LeftShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "{} expects 2 args, got {}", name, args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::domain_error(format!(
                            "shift amount {} out of range (0-63)", b
                        )));
                    }
                    return Ok(Value::Int(a << b));
                }
                "ShiftRight" | "RightShift" => {
                    if args.len() != 2 {
                        return Err(EvalError::domain_error(format!(
                            "{} expects 2 args, got {}", name, args.len()
                        )));
                    }
                    let a = eval_int(&args[0], env, defs)?;
                    let b = eval_int(&args[1], env, defs)?;
                    if !(0..=63).contains(&b) {
                        return Err(EvalError::domain_error(format!(
                            "shift amount {} out of range (0-63)", b
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
                let mut local = env.clone();
                for (param, arg_expr) in params.iter().zip(args) {
                    local.insert(param.clone(), eval(arg_expr, env, defs)?);
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
            Ok(Value::Fn(f))
        }

        Expr::CustomOp(name, _left, _right) => {
            Err(EvalError::domain_error(format!("undefined custom operator: \\{}", name)))
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
                            return Err(EvalError::domain_error("invalid record update path"));
                        }
                    }
                    Value::Fn(fv) => {
                        update_nested(fv, &key_vals, v)?;
                    }
                    _ => {
                        return Err(EvalError::domain_error("EXCEPT requires record or function"))
                    }
                }
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
                    Ok(Value::Set(dom))
                }
                Value::Tuple(seq) => {
                    let dom: BTreeSet<Value> = (1..=seq.len()).map(|i| Value::Int(i as i64)).collect();
                    Ok(Value::Set(dom))
                }
                other => Err(EvalError::type_mismatch_ctx("Fn or Sequence", other, "DOMAIN")),
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
                .ok_or_else(|| EvalError::domain_error(format!("field '{}' not in record", field)))
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
                    .ok_or_else(|| EvalError::domain_error(format!(
                        "sequence index {} out of bounds (sequence has {} elements)",
                        idx + 1, tv.len()
                    ))),
                Value::Fn(fv) => {
                    let key = Value::Int((*idx + 1) as i64);
                    fv.get(&key)
                        .cloned()
                        .ok_or_else(|| EvalError::domain_error(format!(
                            "key {} not in function domain",
                            idx + 1
                        )))
                }
                other => Err(EvalError::TypeMismatch { expected: "Tuple or Fn", got: other, context: Some("tuple access"),  span: None }),
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
                return Err(EvalError::domain_error("SubSeq index out of bounds"));
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
                        return Err(EvalError::domain_error(format!(
                            "SelectSeq test expects 1 parameter, got {}",
                            params.len()
                        )));
                    }
                    let mut local = env.clone();
                    local.insert(params[0].clone(), elem.clone());
                    eval_bool(body, &local, defs)?
                } else {
                    return Err(EvalError::domain_error("SelectSeq test must be a LAMBDA expression"));
                };
                if keep {
                    result.push(elem);
                }
            }
            Ok(Value::Tuple(result))
        }

        Expr::SeqSet(_) => Err(EvalError::domain_error("Seq(S) cannot be enumerated (infinite set); use for membership tests only")),

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

        Expr::JavaTime => Err(EvalError::domain_error("JavaTime is dumb, use SystemTime instead")),

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
            let result: BTreeSet<Value> = perms.into_iter().map(Value::Tuple).collect();
            Ok(Value::Set(result))
        }

        Expr::SortSeq(seq_expr, cmp_expr) => {
            let tv = eval_tuple(seq_expr, env, defs)?;
            let mut result = tv;
            if let Expr::Lambda(params, body) = cmp_expr.as_ref() {
                if params.len() != 2 {
                    return Err(EvalError::domain_error("SortSeq comparator must take exactly 2 arguments"));
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
                return Err(EvalError::domain_error("SortSeq comparator must be a LAMBDA expression"));
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
                return Err(EvalError::domain_error("RandomElement of empty set"));
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
                        other => Err(EvalError::domain_error(format!(
                            "TLCGet: unknown key \"{}\"", other
                        ))),
                    }
                }),
                other => Err(EvalError::TypeMismatch { expected: "Int or Str", got: other, context: Some("TLCGet key"),  span: None }),
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

        Expr::Any => Err(EvalError::domain_error("Any cannot be evaluated directly, only used in membership tests")),

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
                    return Err(EvalError::TypeMismatch { expected: "Bag (Fn)", got: bag_val, context: Some("BagUnion element"),  span: None });
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
                return Err(EvalError::domain_error("SubBag of bag with more than 20 total copies is too large"));
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
                    return Err(EvalError::domain_error("BagOfAll expects a single-argument lambda"));
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
                return Err(EvalError::domain_error("BagOfAll requires a LAMBDA expression"));
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
            Err(EvalError::domain_error("no case matched"))
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

        Expr::Always(_) => Err(EvalError::domain_error("temporal operator [] (always) cannot be evaluated in explicit-state model checking")),

        Expr::Eventually(_) => Err(EvalError::domain_error("temporal operator <> (eventually) cannot be evaluated in explicit-state model checking")),

        Expr::LeadsTo(_, _) => Err(EvalError::domain_error("temporal operator ~> (leads-to) cannot be evaluated in explicit-state model checking")),

        Expr::WeakFairness(_, _) => Err(EvalError::domain_error("temporal operator WF (weak fairness) cannot be evaluated in explicit-state model checking")),

        Expr::StrongFairness(_, _) => Err(EvalError::domain_error("temporal operator SF (strong fairness) cannot be evaluated in explicit-state model checking")),

        Expr::BoxAction(_, _) => Err(EvalError::domain_error("temporal operator [A]_v (box action) cannot be evaluated in explicit-state model checking")),

        Expr::DiamondAction(_, _) => Err(EvalError::domain_error("temporal operator <<A>>_v (diamond action) cannot be evaluated in explicit-state model checking")),

        Expr::EnabledOp(_) => Err(EvalError::domain_error("ENABLED operator cannot be evaluated in explicit-state model checking")),

        Expr::QualifiedCall(instance, op, args) => {
            RESOLVED_INSTANCES.with(|inst_ref| {
                let instances = inst_ref.borrow();
                if instances.is_empty() {
                    return Err(EvalError::domain_error(format!(
                        "qualified call {}!{} requires resolved instances",
                        instance, op
                    )));
                }

                let instance_defs = instances
                    .get(instance)
                    .ok_or_else(|| EvalError::domain_error(format!("instance {} not found", instance)))?;

                let (params, body) = instance_defs
                    .get(op)
                    .ok_or_else(|| EvalError::domain_error(format!(
                        "operator {} not found in instance {}",
                        op, instance
                    )))?;

                if args.len() != params.len() {
                    return Err(EvalError::domain_error(format!(
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
                .ok_or_else(|| EvalError::domain_error(format!("instance {} not found", instance)))?;

            let (params, body) = instance_defs
                .get(op)
                .ok_or_else(|| EvalError::domain_error(format!(
                    "operator {} not found in instance {}",
                    op, instance
                )))?;

            if args.len() != params.len() {
                return Err(EvalError::domain_error(format!(
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
                    return Err(EvalError::domain_error(format!(
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
        other => Err(EvalError::TypeMismatch { expected: "Bool", got: other, context: None,  span: None }),
    }
}

fn eval_bool(expr: &Expr, env: &Env, defs: &Definitions) -> Result<bool> {
    match eval(expr, env, defs)? {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch { expected: "Bool", got: other, context: None,  span: None }),
    }
}

fn eval_int(expr: &Expr, env: &Env, defs: &Definitions) -> Result<i64> {
    match eval(expr, env, defs)? {
        Value::Int(i) => Ok(i),
        other => Err(EvalError::TypeMismatch { expected: "Int", got: other, context: None,  span: None }),
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
        other => Err(EvalError::TypeMismatch { expected: "Set", got: other, context: None,  span: None }),
    }
}

fn eval_fn(expr: &Expr, env: &Env, defs: &Definitions) -> Result<BTreeMap<Value, Value>> {
    match eval(expr, env, defs)? {
        Value::Fn(f) => Ok(f),
        other => Err(EvalError::TypeMismatch { expected: "Fn", got: other, context: None,  span: None }),
    }
}

fn eval_record(expr: &Expr, env: &Env, defs: &Definitions) -> Result<BTreeMap<Arc<str>, Value>> {
    match eval(expr, env, defs)? {
        Value::Record(r) => Ok(r),
        other => Err(EvalError::TypeMismatch { expected: "Record", got: other, context: None,  span: None }),
    }
}

fn eval_tuple(expr: &Expr, env: &Env, defs: &Definitions) -> Result<Vec<Value>> {
    match eval(expr, env, defs)? {
        Value::Tuple(t) => Ok(t),
        other => Err(EvalError::TypeMismatch { expected: "Tuple", got: other, context: None,  span: None }),
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
                .ok_or_else(|| EvalError::domain_error(format!("field '{}' not found", field)))?;
            get_nested(v, &keys[1..])
        }
        (Value::Fn(f), key) => {
            let v = f
                .get(key)
                .ok_or_else(|| EvalError::domain_error(format!(
                    "key {} not in function domain",
                    format_value(key)
                )))?;
            get_nested(v, &keys[1..])
        }
        _ => Err(EvalError::domain_error("cannot access into this value")),
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
        .ok_or_else(|| EvalError::domain_error(format!(
            "key {} not in function domain",
            format_value(&keys[0])
        )))?;
    match inner {
        Value::Fn(inner_fn) => update_nested(inner_fn, &keys[1..], val),
        _ => Err(EvalError::TypeMismatch { expected: "Fn", got: inner.clone(), context: Some("nested EXCEPT update"),  span: None }),
    }
}

pub fn next_states(
    next: &Expr,
    current: &State,
    vars: &[Arc<str>],
    constants: &Env,
    defs: &Definitions,
) -> Result<Vec<State>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let result = next_states_impl(next, current, vars, constants, defs);

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.next_states_time_ns += _start.elapsed().as_nanos();
        stats.next_states_calls += 1;
    });

    result
}

fn next_states_impl(
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
                let mut results = Vec::new();
                expand_and_enumerate(disjunct, &mut base_env, vars, defs, &mut results)?;
                for state in results {
                    all_results.insert(state);
                }
            } else {
                let mut results = Vec::new();
                enumerate_next(disjunct, &mut base_env, vars, 0, defs, &mut results)?;
                for state in results {
                    all_results.insert(state);
                }
            }
        }
        return Ok(all_results.into_iter().collect());
    }

    let mut results = Vec::new();
    enumerate_next(next, &mut base_env, vars, 0, defs, &mut results)?;
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

fn expand_and_enumerate(
    expr: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    match expr {
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, defs)?;
            let var = var.clone();
            for val in dom {
                env.insert(var.clone(), val);
                expand_and_enumerate(body, env, vars, defs, results)?;
            }
            env.remove(&var);
            Ok(())
        }
        _ => enumerate_next(expr, env, vars, 0, defs, results),
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
    check_enabled(action, &mut base_env, vars, 0, defs)
}

fn check_enabled(
    action: &Expr,
    env: &mut Env,
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

    for candidate in candidates {
        env.insert(primed.clone(), candidate);
        if check_enabled(action, env, vars, var_idx + 1, defs)? {
            env.remove(&primed);
            return Ok(true);
        }
    }
    env.remove(&primed);

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

fn contains_prime_ref(expr: &Expr, defs: &Definitions) -> bool {
    match expr {
        Expr::Prime(_) | Expr::Unchanged(_) => true,
        Expr::Var(_) | Expr::Lit(_) | Expr::OldValue | Expr::Any | Expr::EmptyBag
        | Expr::JavaTime | Expr::SystemTime => false,
        Expr::Not(e) | Expr::Neg(e) | Expr::Cardinality(e) | Expr::IsFiniteSet(e)
        | Expr::Powerset(e) | Expr::BigUnion(e) | Expr::Domain(e) | Expr::Len(e)
        | Expr::Head(e) | Expr::Tail(e) | Expr::TransitiveClosure(e)
        | Expr::ReflexiveTransitiveClosure(e) | Expr::SeqSet(e) | Expr::PrintT(e)
        | Expr::Permutations(e) | Expr::TLCToString(e) | Expr::RandomElement(e)
        | Expr::TLCGet(e) | Expr::TLCEval(e) | Expr::IsABag(e) | Expr::BagToSet(e)
        | Expr::SetToBag(e) | Expr::BagUnion(e) | Expr::SubBag(e) | Expr::BagCardinality(e)
        | Expr::Always(e) | Expr::Eventually(e) | Expr::EnabledOp(e) => {
            contains_prime_ref(e, defs)
        }
        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Implies(l, r)
        | Expr::Equiv(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Le(l, r)
        | Expr::Gt(l, r)
        | Expr::Ge(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::Mod(l, r)
        | Expr::Exp(l, r)
        | Expr::BitwiseAnd(l, r)
        | Expr::ActionCompose(l, r)
        | Expr::In(l, r)
        | Expr::NotIn(l, r)
        | Expr::Union(l, r)
        | Expr::Intersect(l, r)
        | Expr::SetMinus(l, r)
        | Expr::Cartesian(l, r)
        | Expr::Subset(l, r)
        | Expr::ProperSubset(l, r)
        | Expr::Concat(l, r)
        | Expr::Append(l, r)
        | Expr::SetRange(l, r)
        | Expr::FnApp(l, r)
        | Expr::FnMerge(l, r)
        | Expr::SingleFn(l, r)
        | Expr::FunctionSet(l, r)
        | Expr::Print(l, r)
        | Expr::Assert(l, r)
        | Expr::TLCSet(l, r)
        | Expr::SortSeq(l, r)
        | Expr::SelectSeq(l, r)
        | Expr::BagIn(l, r)
        | Expr::BagAdd(l, r)
        | Expr::BagSub(l, r)
        | Expr::BagOfAll(l, r)
        | Expr::CopiesIn(l, r)
        | Expr::SqSubseteq(l, r)
        | Expr::LeadsTo(l, r) => contains_prime_ref(l, defs) || contains_prime_ref(r, defs),
        Expr::If(c, t, e) | Expr::SubSeq(c, t, e) => {
            contains_prime_ref(c, defs) || contains_prime_ref(t, defs) || contains_prime_ref(e, defs)
        }
        Expr::Forall(_, d, b) | Expr::Exists(_, d, b) | Expr::Choose(_, d, b)
        | Expr::FnDef(_, d, b) | Expr::SetFilter(_, d, b) | Expr::SetMap(_, d, b)
        | Expr::CustomOp(_, d, b) => {
            contains_prime_ref(d, defs) || contains_prime_ref(b, defs)
        }
        Expr::SetEnum(elems) | Expr::TupleLit(elems) => {
            elems.iter().any(|e| contains_prime_ref(e, defs))
        }
        Expr::RecordLit(fields) | Expr::RecordSet(fields) => {
            fields.iter().any(|(_, e)| contains_prime_ref(e, defs))
        }
        Expr::RecordAccess(r, _) | Expr::TupleAccess(r, _) => contains_prime_ref(r, defs),
        Expr::Except(b, u) => {
            contains_prime_ref(b, defs)
                || u.iter()
                    .any(|(path, val)| path.iter().any(|p| contains_prime_ref(p, defs)) || contains_prime_ref(val, defs))
        }
        Expr::FnCall(name, args) | Expr::QualifiedCall(_, name, args) => {
            if let Some((_, body)) = defs.get(name) {
                contains_prime_ref(body, defs)
            } else {
                args.iter().any(|a| contains_prime_ref(a, defs))
            }
        }
        Expr::Lambda(_, body) => contains_prime_ref(body, defs),
        Expr::Let(_, binding, body) => {
            contains_prime_ref(binding, defs) || contains_prime_ref(body, defs)
        }
        Expr::Case(branches) => branches
            .iter()
            .any(|(c, r)| contains_prime_ref(c, defs) || contains_prime_ref(r, defs)),
        Expr::LabeledAction(_, a) => contains_prime_ref(a, defs),
        Expr::WeakFairness(_, e) | Expr::StrongFairness(_, e)
        | Expr::BoxAction(e, _) | Expr::DiamondAction(e, _) => contains_prime_ref(e, defs),
    }
}

fn collect_conjuncts(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::And(l, r) => {
            let mut result = collect_conjuncts(l);
            result.extend(collect_conjuncts(r));
            result
        }
        _ => vec![expr],
    }
}

fn evaluate_guards(expr: &Expr, env: &Env, defs: &Definitions) -> Result<bool> {
    for conjunct in collect_conjuncts(expr) {
        if !contains_prime_ref(conjunct, defs) && !eval_bool(conjunct, env, defs)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn enumerate_next(
    next: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    var_idx: usize,
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let result = enumerate_next_impl(next, env, vars, var_idx, defs, results);

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.enumerate_next_time_ns += _start.elapsed().as_nanos();
        stats.enumerate_next_calls += 1;
    });

    result
}

fn enumerate_next_impl(
    next: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    var_idx: usize,
    defs: &Definitions,
    results: &mut Vec<State>,
) -> Result<()> {
    if var_idx == 0 && !evaluate_guards(next, env, defs)? {
        return Ok(());
    }

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
        env.insert(primed.clone(), candidate);
        enumerate_next_impl(next, env, vars, var_idx + 1, defs, results)?;
    }
    env.remove(&primed);

    Ok(())
}

fn infer_candidates(next: &Expr, env: &mut Env, var: &Arc<str>, defs: &Definitions) -> Result<Vec<Value>> {
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut candidates = BTreeSet::new();
    collect_candidates(next, env, var, defs, &mut candidates)?;

    if candidates.is_empty()
        && let Some(current) = env.get(var) {
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

fn collect_candidates(
    expr: &Expr,
    env: &mut Env,
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
            if contains_prime_ref(l, defs) {
                collect_candidates(l, env, var, defs, candidates)?;
            }
            if contains_prime_ref(r, defs) {
                collect_candidates(r, env, var, defs, candidates)?;
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
                    collect_candidates(body, env, var, defs, candidates)?;
                }
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
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
                let bound = bound.clone();
                let prev = env.insert(bound.clone(), val);
                collect_candidates(body, env, var, defs, candidates)?;
                match prev {
                    Some(v) => env.insert(bound, v),
                    None => env.remove(&bound),
                };
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
                && contains_prime_ref(body, defs)
            {
                let params: Vec<Arc<str>> = params.clone();
                let mut saved: Vec<(Arc<str>, Option<Value>)> = Vec::new();
                for (param, arg) in params.iter().zip(args.iter()) {
                    if let Ok(val) = eval(arg, env, defs) {
                        let prev = env.insert(param.clone(), val);
                        saved.push((param.clone(), prev));
                    }
                }
                collect_candidates(body, env, var, defs, candidates)?;
                for (param, prev) in saved {
                    match prev {
                        Some(v) => env.insert(param, v),
                        None => env.remove(&param),
                    };
                }
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
    #[cfg(feature = "profiling")]
    let _start = Instant::now();

    let mut results = Vec::new();
    let mut initial_env = domains.clone();
    enumerate_init(init, &mut initial_env, vars, 0, domains, defs, &mut results)?;

    #[cfg(feature = "profiling")]
    PROFILING_STATS.with(|s| {
        let mut stats = s.borrow_mut();
        stats.init_states_time_ns += _start.elapsed().as_nanos();
        stats.init_states_calls += 1;
    });

    Ok(results)
}

fn enumerate_init(
    init: &Expr,
    env: &mut Env,
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

    let var = var.clone();
    for candidate in candidates {
        env.insert(var.clone(), candidate);
        enumerate_init(init, env, vars, var_idx + 1, domains, defs, results)?;
    }
    env.remove(&var);

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

#[derive(Debug, Clone, Copy)]
enum CardinalityConstraint {
    GreaterThan(usize),
    GreaterThanOrEq(usize),
    Equals(usize),
    LessThan(usize),
    LessThanOrEq(usize),
}

fn detect_cardinality_constraint(
    predicate: &Expr,
    var: &Arc<str>,
    env: &Env,
    defs: &Definitions,
) -> Option<CardinalityConstraint> {
    fn is_cardinality_of_var(expr: &Expr, var: &Arc<str>) -> bool {
        matches!(expr, Expr::Cardinality(inner) if matches!(inner.as_ref(), Expr::Var(v) if v == var))
    }

    fn try_eval_int(expr: &Expr, env: &Env, defs: &Definitions) -> Option<i64> {
        match eval(expr, env, defs) {
            Ok(Value::Int(n)) => Some(n),
            _ => None,
        }
    }

    match predicate {
        Expr::Gt(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::GreaterThan(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::LessThan(n as usize))
            } else if let Expr::Mul(card, two) = l.as_ref()
                && is_cardinality_of_var(card, var)
                && let (Some(mult), Some(rhs)) = (try_eval_int(two, env, defs), try_eval_int(r, env, defs))
                && mult == 2
            {
                Some(CardinalityConstraint::GreaterThan((rhs / 2) as usize))
            } else {
                None
            }
        }
        Expr::Ge(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::GreaterThanOrEq(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::LessThanOrEq(n as usize))
            } else {
                None
            }
        }
        Expr::Lt(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::LessThan(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::GreaterThan(n as usize))
            } else {
                None
            }
        }
        Expr::Le(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::LessThanOrEq(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::GreaterThanOrEq(n as usize))
            } else {
                None
            }
        }
        Expr::Eq(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::Equals(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::Equals(n as usize))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn k_combinations<T: Clone>(elements: &[T], k: usize) -> Vec<Vec<T>> {
    let n = elements.len();
    if k > n {
        return vec![];
    }
    if k == 0 {
        return vec![vec![]];
    }
    if k == n {
        return vec![elements.to_vec()];
    }

    let mut result = Vec::new();
    let mut indices: Vec<usize> = (0..k).collect();

    loop {
        result.push(indices.iter().map(|&i| elements[i].clone()).collect());

        let mut i = k as i32 - 1;
        while i >= 0 && indices[i as usize] == n - k + i as usize {
            i -= 1;
        }
        if i < 0 {
            break;
        }

        indices[i as usize] += 1;
        for j in (i as usize + 1)..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
    result
}

fn generate_subsets_with_constraint(
    elements: &[Value],
    constraint: CardinalityConstraint,
) -> BTreeSet<Value> {
    let n = elements.len();
    let (min_k, max_k) = match constraint {
        CardinalityConstraint::GreaterThan(k) => (k + 1, n),
        CardinalityConstraint::GreaterThanOrEq(k) => (k, n),
        CardinalityConstraint::Equals(k) => (k, k),
        CardinalityConstraint::LessThan(k) => (0, k.saturating_sub(1)),
        CardinalityConstraint::LessThanOrEq(k) => (0, k),
    };

    let mut result = BTreeSet::new();
    for k in min_k..=max_k.min(n) {
        for combo in k_combinations(elements, k) {
            let subset: BTreeSet<Value> = combo.into_iter().collect();
            result.insert(Value::Set(subset));
        }
    }
    result
}
