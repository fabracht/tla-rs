mod ast_utils;
mod candidates;
mod combinatorics;
mod context;
mod core;
mod diagnostics;
mod enumerate;
mod error;
mod global_state;
mod helpers;
mod init;
mod recursive;
mod state;

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ast::Expr;

pub type Definitions = BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>;
pub type ResolvedInstances = BTreeMap<Arc<str>, Definitions>;

#[derive(Debug, Clone)]
pub struct ParameterizedInstance {
    pub params: Vec<Arc<str>>,
    pub module_defs: Definitions,
    pub substitutions: Vec<(Arc<str>, Expr)>,
}

pub type ParameterizedInstances = BTreeMap<Arc<str>, ParameterizedInstance>;

pub use self::context::{eval_with_context, eval_with_instances};
pub use self::core::eval;
pub use self::diagnostics::explain_invariant_failure;
pub use self::error::EvalError;
pub use self::global_state::{
    CheckerStats, EvalContext, clear_resolved_instances, reset_tlc_state, set_checker_level,
    set_parameterized_instances, set_random_seed, set_resolved_instances, update_checker_stats,
};
#[cfg(feature = "profiling")]
pub use self::global_state::{
    ProfilingStats, get_profiling_stats, report_profiling_stats, reset_profiling_stats,
};
pub use self::init::init_states;
pub use self::state::{
    is_action_enabled, make_primed_names, next_states, next_states_with_guards, state_to_env,
};

pub(crate) use self::ast_utils::contains_prime_ref;

pub(crate) fn resolve_parameterized_defs(
    param_inst: &ParameterizedInstance,
    inst_arg_vals: Vec<crate::ast::Value>,
) -> Definitions {
    use crate::substitution::{apply_substitutions, substitute_expr};

    let param_subs: Vec<(Arc<str>, Expr)> = param_inst
        .params
        .iter()
        .zip(inst_arg_vals)
        .map(|(param, val)| (param.clone(), Expr::Lit(val)))
        .collect();

    let substituted_subs: Vec<(Arc<str>, Expr)> = param_inst
        .substitutions
        .iter()
        .map(|(name, expr)| (name.clone(), substitute_expr(expr, &param_subs)))
        .collect();

    let mut all_subs = param_subs;
    all_subs.extend(substituted_subs);
    apply_substitutions(&param_inst.module_defs, &all_subs)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::Arc;

    use crate::ast::{Env, Expr, State, Value};

    use super::*;

    fn var(name: &str) -> Arc<str> {
        Arc::from(name)
    }

    fn lit_int(n: i64) -> Expr {
        Expr::Lit(Value::Int(n))
    }

    fn lit_bool(b: bool) -> Expr {
        Expr::Lit(Value::Bool(b))
    }

    fn var_expr(name: &str) -> Expr {
        Expr::Var(var(name))
    }

    fn prime_expr(name: &str) -> Expr {
        Expr::Prime(var(name))
    }

    fn eq(l: Expr, r: Expr) -> Expr {
        Expr::Eq(Box::new(l), Box::new(r))
    }

    fn and(l: Expr, r: Expr) -> Expr {
        Expr::And(Box::new(l), Box::new(r))
    }

    fn or(l: Expr, r: Expr) -> Expr {
        Expr::Or(Box::new(l), Box::new(r))
    }

    fn add(l: Expr, r: Expr) -> Expr {
        Expr::Add(Box::new(l), Box::new(r))
    }

    fn in_set(elem: Expr, set: Expr) -> Expr {
        Expr::In(Box::new(elem), Box::new(set))
    }

    fn set_range(lo: Expr, hi: Expr) -> Expr {
        Expr::SetRange(Box::new(lo), Box::new(hi))
    }

    fn set_enum(elems: Vec<Expr>) -> Expr {
        Expr::SetEnum(elems)
    }

    fn defs() -> Definitions {
        BTreeMap::new()
    }

    #[test]
    fn eval_bool_true() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&lit_bool(true), &mut env, &d).unwrap();
        assert_eq!(result, Value::Bool(true));
    }

    #[test]
    fn eval_bool_false() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&lit_bool(false), &mut env, &d).unwrap();
        assert_eq!(result, Value::Bool(false));
    }

    #[test]
    fn eval_int_literal() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&lit_int(42), &mut env, &d).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn eval_addition() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&add(lit_int(3), lit_int(4)), &mut env, &d).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn eval_variable_lookup() {
        let d = defs();
        let mut env = Env::new();
        env.insert(var("x"), Value::Int(10));
        let result = eval(&var_expr("x"), &mut env, &d).unwrap();
        assert_eq!(result, Value::Int(10));
    }

    #[test]
    fn eval_undefined_variable() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&var_expr("unknown"), &mut env, &d);
        assert!(result.is_err());
    }

    #[test]
    fn eval_set_enum() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(
            &set_enum(vec![lit_int(1), lit_int(2), lit_int(3)]),
            &mut env,
            &d,
        )
        .unwrap();
        let expected: BTreeSet<Value> = [Value::Int(1), Value::Int(2), Value::Int(3)].into();
        assert_eq!(result, Value::Set(expected));
    }

    #[test]
    fn eval_set_range() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(&set_range(lit_int(1), lit_int(3)), &mut env, &d).unwrap();
        let expected: BTreeSet<Value> = [Value::Int(1), Value::Int(2), Value::Int(3)].into();
        assert_eq!(result, Value::Set(expected));
    }

    #[test]
    fn eval_in_set() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(
            &in_set(
                lit_int(2),
                set_enum(vec![lit_int(1), lit_int(2), lit_int(3)]),
            ),
            &mut env,
            &d,
        )
        .unwrap();
        assert_eq!(result, Value::Bool(true));
    }

    #[test]
    fn eval_not_in_set() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(
            &in_set(lit_int(5), set_enum(vec![lit_int(1), lit_int(2)])),
            &mut env,
            &d,
        )
        .unwrap();
        assert_eq!(result, Value::Bool(false));
    }

    #[test]
    fn eval_in_int_range() {
        let d = defs();
        let mut env = Env::new();
        let result = eval(
            &in_set(lit_int(2), set_range(lit_int(1), lit_int(5))),
            &mut env,
            &d,
        )
        .unwrap();
        assert_eq!(result, Value::Bool(true));
    }

    #[test]
    fn eval_equality() {
        let d = defs();
        let mut env = Env::new();
        assert_eq!(
            eval(&eq(lit_int(1), lit_int(1)), &mut env, &d).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&eq(lit_int(1), lit_int(2)), &mut env, &d).unwrap(),
            Value::Bool(false)
        );
    }

    #[test]
    fn eval_conjunction() {
        let d = defs();
        let mut env = Env::new();
        assert_eq!(
            eval(&and(lit_bool(true), lit_bool(true)), &mut env, &d).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&and(lit_bool(true), lit_bool(false)), &mut env, &d).unwrap(),
            Value::Bool(false)
        );
    }

    #[test]
    fn eval_disjunction() {
        let d = defs();
        let mut env = Env::new();
        assert_eq!(
            eval(&or(lit_bool(false), lit_bool(true)), &mut env, &d).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&or(lit_bool(false), lit_bool(false)), &mut env, &d).unwrap(),
            Value::Bool(false)
        );
    }

    #[test]
    fn init_states_simple() {
        let d = defs();
        let env = Env::new();
        let vars = vec![var("x")];
        let init = eq(var_expr("x"), lit_int(0));
        let states = init_states(&init, &vars, &env, &d).unwrap();
        assert_eq!(states.len(), 1);
        assert_eq!(states[0].values, vec![Value::Int(0)]);
    }

    #[test]
    fn init_states_multiple() {
        let d = defs();
        let env = Env::new();
        let vars = vec![var("x")];
        let init = in_set(var_expr("x"), set_enum(vec![lit_int(1), lit_int(2)]));
        let states = init_states(&init, &vars, &env, &d).unwrap();
        assert_eq!(states.len(), 2);
    }

    #[test]
    fn next_states_counter() {
        let d = defs();
        let mut env = Env::new();
        let vars = vec![var("count")];
        let primed = make_primed_names(&vars);
        let current = State {
            values: vec![Value::Int(0)],
        };
        let next_expr = and(
            in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
            eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
        );
        let successors = next_states(&next_expr, &current, &vars, &primed, &mut env, &d).unwrap();
        assert_eq!(successors.len(), 1);
        assert_eq!(successors[0].state.values, vec![Value::Int(1)]);
    }

    #[test]
    fn next_states_deadlock() {
        let d = defs();
        let mut env = Env::new();
        let vars = vec![var("count")];
        let primed = make_primed_names(&vars);
        let current = State {
            values: vec![Value::Int(3)],
        };
        let next_expr = and(
            in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
            eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
        );
        let successors = next_states(&next_expr, &current, &vars, &primed, &mut env, &d).unwrap();
        assert_eq!(successors.len(), 0);
    }

    #[test]
    fn make_primed_names_correct() {
        let vars = vec![var("x"), var("y")];
        let primed = make_primed_names(&vars);
        assert_eq!(primed.len(), 2);
        assert_eq!(primed[0].as_ref(), "x'");
        assert_eq!(primed[1].as_ref(), "y'");
    }

    #[test]
    fn eval_if_then_else() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::If(
            Box::new(lit_bool(true)),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Int(1));

        let expr2 = Expr::If(
            Box::new(lit_bool(false)),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        assert_eq!(eval(&expr2, &mut env, &d).unwrap(), Value::Int(2));
    }

    #[test]
    fn eval_let_binding() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::Let(
            var("x"),
            Box::new(lit_int(5)),
            Box::new(add(var_expr("x"), lit_int(1))),
        );
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Int(6));
    }

    #[test]
    fn eval_forall() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::Forall(
            var("x"),
            Box::new(set_enum(vec![lit_int(1), lit_int(2), lit_int(3)])),
            Box::new(Expr::Gt(Box::new(var_expr("x")), Box::new(lit_int(0)))),
        );
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_exists() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::Exists(
            var("x"),
            Box::new(set_enum(vec![lit_int(1), lit_int(2), lit_int(3)])),
            Box::new(eq(var_expr("x"), lit_int(2))),
        );
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eval_function_definition() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::FnDef(
            var("x"),
            Box::new(set_enum(vec![lit_int(1), lit_int(2)])),
            Box::new(add(var_expr("x"), lit_int(10))),
        );
        let result = eval(&expr, &mut env, &d).unwrap();
        if let Value::Fn(f) = result {
            assert_eq!(f.get(&Value::Int(1)), Some(&Value::Int(11)));
            assert_eq!(f.get(&Value::Int(2)), Some(&Value::Int(12)));
        } else {
            panic!("expected Fn");
        }
    }

    #[test]
    fn eval_function_application() {
        let d = defs();
        let mut env = Env::new();
        let fn_def = Expr::FnDef(
            var("x"),
            Box::new(set_enum(vec![lit_int(1), lit_int(2)])),
            Box::new(add(var_expr("x"), lit_int(10))),
        );
        let app = Expr::FnApp(Box::new(fn_def), Box::new(lit_int(1)));
        assert_eq!(eval(&app, &mut env, &d).unwrap(), Value::Int(11));
    }

    #[test]
    fn eval_record_literal() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::RecordLit(vec![(var("a"), lit_int(1)), (var("b"), lit_int(2))]);
        let result = eval(&expr, &mut env, &d).unwrap();
        if let Value::Record(r) = result {
            assert_eq!(r.get(&var("a")), Some(&Value::Int(1)));
            assert_eq!(r.get(&var("b")), Some(&Value::Int(2)));
        } else {
            panic!("expected Record");
        }
    }

    #[test]
    fn eval_tuple_literal() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::TupleLit(vec![lit_int(10), lit_int(20)]);
        let result = eval(&expr, &mut env, &d).unwrap();
        assert_eq!(result, Value::Tuple(vec![Value::Int(10), Value::Int(20)]));
    }

    #[test]
    fn eval_cardinality() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::Cardinality(Box::new(set_enum(vec![lit_int(1), lit_int(2), lit_int(3)])));
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Int(3));
    }

    #[test]
    fn eval_definition_call() {
        let mut d = defs();
        d.insert(
            var("Double"),
            (vec![var("n")], add(var_expr("n"), var_expr("n"))),
        );
        let mut env = Env::new();
        let expr = Expr::FnCall(var("Double"), vec![lit_int(5)]);
        assert_eq!(eval(&expr, &mut env, &d).unwrap(), Value::Int(10));
    }

    #[test]
    fn eval_division_by_zero() {
        let d = defs();
        let mut env = Env::new();
        let expr = Expr::Div(Box::new(lit_int(10)), Box::new(lit_int(0)));
        let result = eval(&expr, &mut env, &d);
        assert!(result.is_err());
    }

    #[test]
    fn state_to_env_roundtrip() {
        let vars = vec![var("x"), var("y")];
        let state = State {
            values: vec![Value::Int(1), Value::Int(2)],
        };
        let env = state_to_env(&state, &vars);
        assert_eq!(env.get(&var("x")), Some(&Value::Int(1)));
        assert_eq!(env.get(&var("y")), Some(&Value::Int(2)));
    }
}
