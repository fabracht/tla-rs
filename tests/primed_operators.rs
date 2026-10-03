use tla_checker::ast::Env;
use tla_checker::parser::parse;
use tla_checker::scenario::{execute_scenario, parse_scenario};

/// Priming a defined operator evaluates its body in the next state. Bound
/// variables and constants have no primed counterpart and must be left alone.
const SPEC: &str = r#"---- MODULE primed ----
EXTENDS Integers
VARIABLES x
Limit == 2
Init == x = 0
Inc == x < 4 /\ x' = x + 1
Next == Inc
Small == x < Limit
EveryoneSmall == \A i \in {1, 2} : x < Limit
===="#;

fn replay(scenario: &str) -> Result<bool, String> {
    let spec = parse(SPEC).expect("spec parses");
    let steps = parse_scenario(scenario).map_err(|e| e.to_string())?;
    let result = execute_scenario(&spec, &steps, &Env::new()).map_err(|e| e.to_string())?;
    Ok(result.failure.is_none())
}

#[test]
fn primed_operator_reads_the_next_state() {
    assert_eq!(replay("action: Inc; x' = 1 /\\ Small'\n"), Ok(true));
    assert_eq!(replay("action: Inc; x' = 1 /\\ ~Small'\n"), Ok(false));
}

#[test]
fn primed_operator_tracks_the_state_it_is_evaluated_in() {
    let holds = "action: Inc; x' = 1\naction: Inc; x' = 2 /\\ ~Small'\n";
    assert_eq!(replay(holds), Ok(true));
    let fails = "action: Inc; x' = 1\naction: Inc; x' = 2 /\\ Small'\n";
    assert_eq!(replay(fails), Ok(false));
}

#[test]
fn priming_leaves_bound_variables_and_constant_operators_alone() {
    assert_eq!(replay("action: Inc; x' = 1 /\\ EveryoneSmall'\n"), Ok(true));
    assert_eq!(
        replay("action: Inc; x' = 1\naction: Inc; x' = 2 /\\ ~EveryoneSmall'\n"),
        Ok(true)
    );
}

#[test]
fn unknown_primed_name_is_still_an_error() {
    let message = replay("action: Inc; Missing'\n").expect_err("undefined name");
    assert!(message.contains("Missing"), "{message}");
}

#[test]
fn priming_outside_a_next_state_context_is_an_error() {
    use tla_checker::ast::Value;
    use tla_checker::eval::eval;
    use tla_checker::parser::parse_expr;
    use tla_checker::scenario::build_definitions;

    let spec = parse(SPEC).expect("spec parses");
    let defs = build_definitions(&spec);
    let expr = parse_expr("Small'").expect("expression parses");

    let mut current_only = Env::new();
    current_only.insert(tla_checker::intern::intern("x"), Value::Int(0));
    let err = eval(&expr, &mut current_only, &defs).expect_err("no next state in scope");
    assert!(err.to_string().contains("no next-state values"), "{err}");

    let mut with_next = current_only.clone();
    with_next.insert(tla_checker::intern::intern("x'"), Value::Int(1));
    assert_eq!(
        eval(&expr, &mut with_next, &defs).expect("evaluates in the next state"),
        Value::Bool(true)
    );
}
