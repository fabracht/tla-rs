use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

use crate::ast::{Env, Expr, Value};

use super::Definitions;
use super::core::{STACK_GROWTH, STACK_RED_ZONE, eval};
use super::error::{EvalError, Result, value_type_name};
use crate::checker::format_value;

struct RecursiveFunction {
    name: Arc<str>,
    body: *const Expr,
    domain: FunctionDomain,
    values: RefCell<BTreeMap<Value, Value>>,
}

/// The domain of a function being evaluated: the values it is built for, or, for
/// a function applied to an argument, the set its argument must belong to, so
/// only the points the application needs are evaluated, as in TLC.
enum FunctionDomain {
    Values(BTreeSet<Value>),
    Set(Expr),
}

impl RecursiveFunction {
    /// Whether `name` refers to this function in `defs`, and not to another
    /// function of the same name, as a `LET` inside its evaluation may define.
    fn is(&self, name: &Arc<str>, body: &Expr) -> bool {
        &self.name == name && std::ptr::eq(self.body, body)
    }
}

impl FunctionDomain {
    fn contains(&self, key: &Value, env: &mut Env, defs: &Definitions) -> Result<bool> {
        match self {
            FunctionDomain::Values(values) => Ok(values.contains(key)),
            FunctionDomain::Set(set) => {
                let membership = Expr::In(Box::new(Expr::Lit(key.clone())), Box::new(set.clone()));
                match eval(&membership, env, defs)? {
                    Value::Bool(member) => Ok(member),
                    other => Err(EvalError::type_mismatch_ctx(
                        "Bool",
                        other,
                        "function domain",
                    )),
                }
            }
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

pub(crate) fn eval_fn_def_recursive(
    fn_name: &Arc<str>,
    param: &Arc<str>,
    domain: BTreeSet<Value>,
    body: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<BTreeMap<Value, Value>> {
    let function = Rc::new(RecursiveFunction {
        name: fn_name.clone(),
        body,
        domain: FunctionDomain::Values(domain.clone()),
        values: RefCell::new(BTreeMap::new()),
    });
    let active = ActiveFunction::enter(&function);
    let prev = env.remove(param);
    let result = domain.iter().try_for_each(|val| {
        if function.values.borrow().contains_key(val) {
            return Ok(());
        }
        env.insert(param.clone(), val.clone());
        let value = eval_with_memo(body, env, defs, &function)?;
        function.values.borrow_mut().insert(val.clone(), value);
        Ok(())
    });
    match prev {
        Some(old) => {
            env.insert(param.clone(), old);
        }
        None => {
            env.remove(param);
        }
    }
    drop(active);
    result.map(|()| function.values.take())
}

/// `name[arg]` for the function `name[param \in domain] == body`, evaluated
/// only at the points the application reaches, each once: `fact[n \in Nat]`
/// applied to 4 evaluates `fact` at 4, 3, 2, 1 and 0.
pub(crate) fn apply_function_definition(
    name: &Arc<str>,
    param: &Arc<str>,
    domain: &Expr,
    body: &Expr,
    arg: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Result<Value> {
    let key = eval(arg, env, defs)?;
    let function = Rc::new(RecursiveFunction {
        name: name.clone(),
        body,
        domain: FunctionDomain::Set(domain.clone()),
        values: RefCell::new(BTreeMap::new()),
    });
    let active = ActiveFunction::enter(&function);
    let result = apply_memoized(param, body, key, env, defs, &function);
    drop(active);
    result
}

pub(crate) fn apply_active_function(
    name: &Arc<str>,
    arg: &Expr,
    env: &mut Env,
    defs: &Definitions,
) -> Option<Result<Value>> {
    let (param, body) = recursive_definition(name, defs)?;
    let function = ACTIVE_FUNCTIONS
        .with_borrow(|active| active.iter().rev().find(|f| f.is(name, body)).cloned())?;
    Some(
        eval(arg, env, defs).and_then(|key| apply_memoized(param, body, key, env, defs, &function)),
    )
}

fn recursive_definition<'a>(
    name: &Arc<str>,
    defs: &'a Definitions,
) -> Option<(&'a Arc<str>, &'a Expr)> {
    match defs.get(name) {
        Some((params, definition)) if params.is_empty() => match definition.as_ref() {
            Expr::FnDef(param, _, body) => Some((param, body.as_ref())),
            _ => None,
        },
        _ => None,
    }
}

fn apply_memoized(
    param: &Arc<str>,
    body: &Expr,
    key: Value,
    env: &mut Env,
    defs: &Definitions,
    function: &RecursiveFunction,
) -> Result<Value> {
    if !function.domain.contains(&key, env, defs)? {
        return Err(EvalError::domain_error(format!(
            "key {} not in function domain",
            format_value(&key)
        )));
    }
    let cached = function.values.borrow().get(&key).cloned();
    if let Some(value) = cached {
        return Ok(value);
    }
    let prev = env.insert(param.clone(), key.clone());
    let result = eval_with_memo(body, env, defs, function);
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
                && let Some((param, body)) = recursive_definition(name, defs)
                && function.is(name, body)
            {
                let key = eval_with_memo(arg, env, defs, function)?;
                return apply_memoized(param, body, key, env, defs, function);
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
