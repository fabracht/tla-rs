use tla_checker::ast::Env;
use tla_checker::parser::parse;
use tla_checker::scenario::{
    ScenarioResult, build_definitions, execute_scenario_stuttering, parse_scenario,
};

/// A program that only reports `x` crossing 3 produces a trace that skips the
/// spec's intermediate increments.
const SPEC: &str = r#"---- MODULE counting ----
EXTENDS Integers
VARIABLES x
Init == x = 0
Bump == x < 9 /\ x' = x + 1
Next == Bump
===="#;

fn replay(scenario: &str, max_stutter: usize) -> ScenarioResult {
    let spec = parse(SPEC).expect("spec parses");
    let steps = parse_scenario(scenario).expect("scenario parses");
    let defs = build_definitions(&spec);
    execute_scenario_stuttering(&spec, &steps, &Env::new(), &defs, max_stutter)
        .expect("replay runs")
}

#[test]
fn unobserved_transitions_are_taken_within_the_budget() {
    let result = replay("step: x' = 3\n", 2);
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.stutters, 2);
}

#[test]
fn a_budget_too_small_still_rejects() {
    let result = replay("step: x' = 3\n", 1);
    let failure = result.failure.expect("two unobserved steps are needed");
    assert!(
        failure.message.contains("within 1 unobserved steps"),
        "message should name the budget: {}",
        failure.message
    );
}

#[test]
fn a_matching_step_costs_no_stutter() {
    let result = replay("step: x' = 1\n", 4);
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.stutters, 0);
}

#[test]
fn stuttering_is_counted_across_steps() {
    let result = replay("step: x' = 2\nstep: x' = 5\n", 3);
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.stutters, 3);
}
