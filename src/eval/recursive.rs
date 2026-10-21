use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

use crate::ast::{Env, Expr, IntDomain, Value};

use super::Definitions;
use super::core::{STACK_GROWTH, STACK_RED_ZONE, eval};
use super::error::{EvalError, Result, value_type_name};
use super::helpers::{eval_set, in_set_symbolic, is_symbolic_set_expr};
use crate::checker::format_value;

/// A function definition `f[param \in domain] == body`, or the constructor
/// `[param \in domain |-> body]`.
pub(crate) struct FunctionDefinition<'a> {
    pub(crate) param: &'a Arc<str>,
    pub(crate) domain: &'a Expr,
    pub(crate) body: &'a Expr,
}

impl<'a> FunctionDefinition<'a> {
    pub(crate) fn of(expr: &'a Expr) -> Option<Self> {
        match expr {
            Expr::FnDef(param, domain, body) => Some(FunctionDefinition {
                param,
                domain,
                body,
            }),
            _ => None,
        }
    }
}

/// The function `name` stands for in `defs`, when it is a definition without
/// parameters whose body is a function.
pub(crate) fn function_definition<'a>(
    name: &Arc<str>,
    defs: &'a Definitions,
) -> Option<FunctionDefinition<'a>> {
    match defs.get(name) {
        Some((params, definition)) if params.is_empty() => FunctionDefinition::of(definition),
        _ => None,
    }
}

/// A named function being evaluated, with the values computed so far. Its
/// domain is resolved once, the first time an argument is checked: only the
/// points an application reaches are evaluated, as in TLC.
struct RecursiveFunction {
    name: Arc<str>,
    body: *const Expr,
    domain: RefCell<Option<ResolvedDomain>>,
    values: RefCell<BTreeMap<Value, Value>>,
    whole: RefCell<Option<Value>>,
    filled: Cell<bool>,
}

/// A function's domain: its values, an infinite set of integers, or a set
/// whose membership is decided without enumerating it.
enum ResolvedDomain {
    Values(BTreeSet<Value>),
    Integers(IntDomain),
    Symbolic,
}

impl ResolvedDomain {
    fn resolve(domain: &Expr, env: &mut Env, defs: &Definitions) -> Result<Self> {
        if is_symbolic_set_expr(domain, env, defs)? {
            return Ok(ResolvedDomain::Symbolic);
        }
        match eval(domain, env, defs)? {
            Value::Set(values) => Ok(ResolvedDomain::Values(Arc::unwrap_or_clone(values))),
            Value::IntSet(integers) => Ok(ResolvedDomain::Integers(integers)),
            other => Err(EvalError::type_mismatch("Set", other)),
        }
    }
}

impl RecursiveFunction {
    fn new(
        name: Arc<str>,
        definition: &FunctionDefinition,
        domain: Option<BTreeSet<Value>>,
    ) -> Self {
        RecursiveFunction {
            name,
            body: definition.body,
            domain: RefCell::new(domain.map(ResolvedDomain::Values)),
            values: RefCell::new(BTreeMap::new()),
            whole: RefCell::new(None),
            filled: Cell::new(false),
        }
    }

    /// Whether `name` refers to this function in `defs`, and not to another
    /// function of the same name, as a `LET` inside its evaluation may define.
    fn is(&self, name: &Arc<str>, body: &Expr) -> bool {
        &self.name == name && std::ptr::eq(self.body, body)
    }

    /// The points of a finite domain before `key`, in order, the first time a
    /// point is missing: a recursion that reads the points below the one asked
    /// for then finds them computed instead of descending through all of them.
    fn points_before(&self, key: &Value) -> Vec<Value> {
        if self.filled.replace(true) {
            return Vec::new();
        }
        match self.domain.borrow().as_ref() {
            Some(ResolvedDomain::Values(values)) => values.range(..key).cloned().collect(),
            _ => Vec::new(),
        }
    }

    fn contains(
        &self,
        key: &Value,
        definition: &FunctionDefinition,
        env: &mut Env,
        defs: &Definitions,
    ) -> Result<bool> {
        if self.domain.borrow().is_none() {
            let resolved = ResolvedDomain::resolve(definition.domain, env, defs)?;
            self.domain.replace(Some(resolved));
        }
        let decided = match self.domain.borrow().as_ref() {
            Some(ResolvedDomain::Values(values)) => Some(values.contains(key)),
            Some(ResolvedDomain::Integers(integers)) => Some(integers.contains(key)),
            Some(ResolvedDomain::Symbolic) | None => None,
        };
        match decided {
            Some(member) => Ok(member),
            None => in_set_symbolic(key, definition.domain, env, defs),
        }
    }
}

thread_local! {
    static ACTIVE_FUNCTIONS: RefCell<Vec<Rc<RecursiveFunction>>> = const { RefCell::new(Vec::new()) };
}

struct ActiveFunction;

impl ActiveFunction {
    fn enter(function: &Rc<RecursiveFunction>) -> Self {
        ACTIVE_FUNCTIONS.with_borrow_mut(|active| active.push(function.clone()));
        ActiveFunction
    }
}

impl Drop for ActiveFunction {
    fn drop(&mut self) {
        ACTIVE_FUNCTIONS.with_borrow_mut(|active| active.pop());
    }
}

fn active_function(
    name: &Arc<str>,
    definition: &FunctionDefinition,
) -> Option<Rc<RecursiveFunction>> {
    ACTIVE_FUNCTIONS.with_borrow(|active| {
        active
            .iter()
            .rev()
            .find(|function| function.is(name, definition.body))
            .cloned()
    })
}

/// Evaluates `body` with the function `name` of `defs` active, so its
/// applications in `body` share one set of computed values: those of a `LET`
/// function, evaluated once per evaluation of the `LET`.
pub(crate) fn with_function<T>(name: &Arc<str>, defs: &Definitions, body: impl FnOnce() -> T) -> T {
    let Some(definition) = function_definition(name, defs) else {
        return body();
    };
    let function = Rc::new(RecursiveFunction::new(name.clone(), &definition, None));
    let active = ActiveFunction::enter(&function);
    let result = body();
    drop(active);
    result
}

/// The whole function `definition`, built over its domain; `name` is the
/// definition it is the body of, through which it may call itself.
pub(crate) fn function_value(
    name: Option<&Arc<str>>,
    definition: &FunctionDefinition,
    env: &mut Env,
    defs: &Definitions,
) -> Result<Value> {
    let active = name.and_then(|name| active_function(name, definition));
    if let Some(function) = &active
        && let Some(whole) = function.whole.borrow().clone()
    {
        return Ok(whole);
    }
    let domain = eval_set(definition.domain, env, defs)?;
    let function = match active {
        Some(function) => {
            function
                .domain
                .replace(Some(ResolvedDomain::Values(domain.clone())));
            function
        }
        None => Rc::new(RecursiveFunction::new(
            name.cloned().unwrap_or_else(|| Arc::from("")),
            definition,
            Some(domain.clone()),
        )),
    };
    let entered = name.map(|_| ActiveFunction::enter(&function));
    let mut values = BTreeMap::new();
    let result = domain.into_iter().try_for_each(|key| {
        let value = apply_memoized(definition, key.clone(), env, defs, &function)?;
        values.insert(key, value);
        Ok(())
    });
    drop(entered);
    result?;
    let whole = Value::func(values);
    function.whole.replace(Some(whole.clone()));
    Ok(whole)
}

/// The function `definition` applied to `key`, evaluated only at the points the
/// application reaches, each once: `fact[n \in Nat]` applied to 4 evaluates
/// `fact` at 4, 3, 2, 1 and 0. An application inside the function, or inside a
/// [`with_function`] scope, reuses the values computed so far.
pub(crate) fn apply_function(
    name: Option<&Arc<str>>,
    definition: &FunctionDefinition,
    key: Value,
    env: &mut Env,
    defs: &Definitions,
) -> Result<Value> {
    if let Some(function) = name.and_then(|name| active_function(name, definition)) {
        return apply_memoized(definition, key, env, defs, &function);
    }
    let function = Rc::new(RecursiveFunction::new(
        name.cloned().unwrap_or_else(|| Arc::from("")),
        definition,
        None,
    ));
    let entered = name.map(|_| ActiveFunction::enter(&function));
    let result = apply_memoized(definition, key, env, defs, &function);
    drop(entered);
    result
}

fn apply_memoized(
    definition: &FunctionDefinition,
    key: Value,
    env: &mut Env,
    defs: &Definitions,
    function: &RecursiveFunction,
) -> Result<Value> {
    let cached = function.values.borrow().get(&key).cloned();
    if let Some(value) = cached {
        return Ok(value);
    }
    if !function.contains(&key, definition, env, defs)? {
        return Err(EvalError::domain_error(format!(
            "key {} not in function domain",
            format_value(&key)
        )));
    }
    for point in function.points_before(&key) {
        let missing = !function.values.borrow().contains_key(&point);
        if missing {
            evaluate_point(definition, point, env, defs, function).ok();
        }
    }
    evaluate_point(definition, key, env, defs, function)
}

/// The value of the function at `key`, recorded for later applications; a point
/// whose value fails to evaluate is not recorded, so its error is reported only
/// where the point is needed.
fn evaluate_point(
    definition: &FunctionDefinition,
    key: Value,
    env: &mut Env,
    defs: &Definitions,
    function: &RecursiveFunction,
) -> Result<Value> {
    let param = definition.param;
    let prev = env.insert(param.clone(), key.clone());
    let result = eval_with_memo(definition.body, env, defs, function);
    match prev {
        Some(old) => {
            env.insert(param.clone(), old);
        }
        None => {
            env.remove(param);
        }
    }
    let value = result?;
    function.values.borrow_mut().insert(key, value.clone());
    Ok(value)
}

fn eval_with_memo(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    function: &RecursiveFunction,
) -> Result<Value> {
    stacker::maybe_grow(STACK_RED_ZONE, STACK_GROWTH, || {
        eval_with_memo_inner(expr, env, defs, function)
    })
}

fn eval_with_memo_inner(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    function: &RecursiveFunction,
) -> Result<Value> {
    match expr {
        Expr::FnApp(f, arg) => {
            if let Expr::Var(name) = f.as_ref()
                && !env.contains_key(name)
                && let Some(definition) = function_definition(name, defs)
                && function.is(name, definition.body)
            {
                let key = eval_with_memo(arg, env, defs, function)?;
                return apply_memoized(&definition, key, env, defs, function);
            }
            eval(expr, env, defs)
        }

        Expr::Let(var, binding, body) => {
            if let Some((params, op_body)) = super::ast_utils::parameterized_let_op(binding) {
                let mut local_defs = defs.clone();
                local_defs.insert(var.clone(), (params, Arc::new(op_body.clone())));
                return eval_with_memo(body, env, &local_defs, function);
            }
            if matches!(binding.as_ref(), Expr::FnDef(..)) {
                return eval(expr, env, defs);
            }
            if super::ast_utils::is_operator_reference(binding, env, defs) {
                let mut local_defs = defs.clone();
                local_defs.insert(var.clone(), (vec![], Arc::new((**binding).clone())));
                return eval_with_memo(body, env, &local_defs, function);
            }
            let substituted =
                crate::substitution::substitute_expr(body, &[(var.clone(), (**binding).clone())]);
            eval_with_memo(&substituted, env, defs, function)
        }

        Expr::If(cond, then_br, else_br) => {
            let cv = eval_with_memo(cond, env, defs, function)?;
            match cv {
                Value::Bool(true) => eval_with_memo(then_br, env, defs, function),
                Value::Bool(false) => eval_with_memo(else_br, env, defs, function),
                _ => Err(EvalError::type_mismatch_ctx("Bool", cv, "IF condition")),
            }
        }

        Expr::Add(l, r) => {
            let lv = eval_with_memo(l, env, defs, function)?;
            let rv = eval_with_memo(r, env, defs, function)?;
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
            let lv = eval_with_memo(l, env, defs, function)?;
            let rv = eval_with_memo(r, env, defs, function)?;
            Ok(Value::Bool(lv == rv))
        }

        Expr::SetMinus(l, r) => {
            let lv = eval_with_memo(l, env, defs, function)?;
            let rv = eval_with_memo(r, env, defs, function)?;
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
                result.insert(eval_with_memo(e, env, defs, function)?);
            }
            Ok(Value::set(result))
        }

        Expr::Var(name) => {
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            match defs.get(name) {
                Some((params, body))
                    if params.is_empty() && !matches!(body.as_ref(), Expr::FnDef(..)) =>
                {
                    eval_with_memo(body, env, defs, function)
                }
                Some(_) => eval(expr, env, defs),
                None => Err(EvalError::undefined_var_with_env(name.clone(), env, defs)),
            }
        }

        _ => eval(expr, env, defs),
    }
}
