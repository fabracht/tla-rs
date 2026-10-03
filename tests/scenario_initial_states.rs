use tla_checker::ast::Env;
use tla_checker::parser::parse;
use tla_checker::scenario::{ScenarioResult, build_definitions, execute_scenario, parse_scenario};

/// `Init` admits three states here, and only one of them can take the step the
/// scenario asks for.
const SPEC: &str = r#"---- MODULE starts ----
EXTENDS Integers
VARIABLES x
Init == x \in {0, 1, 2}
Bump == x < 9 /\ x' = x + 10
Next == Bump
===="#;

fn replay(scenario: &str) -> ScenarioResult {
    let spec = parse(SPEC).expect("spec parses");
    let steps = parse_scenario(scenario).expect("scenario parses");
    execute_scenario(&spec, &steps, &Env::new()).expect("replay runs")
}

#[test]
fn replay_tries_every_initial_state_until_one_admits_the_scenario() {
    let result = replay("action: Bump; x' = 12\n");
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.init_count, 3);
    assert_eq!(result.init_index, 2);
}

#[test]
fn first_initial_state_is_used_when_it_already_fits() {
    let result = replay("action: Bump; x' = 10\n");
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.init_index, 0);
}

#[test]
fn failure_reports_that_several_initial_states_were_tried() {
    let result = replay("action: Bump; x' = 99\n");
    let failure = result.failure.expect("no initial state admits this step");
    assert_eq!(result.init_count, 3);
    assert!(
        failure.message.contains("of 3"),
        "message should say how many initial states were tried: {}",
        failure.message
    );
}

#[test]
fn definitions_are_reusable_by_embedders() {
    let spec = parse(SPEC).expect("spec parses");
    let defs = build_definitions(&spec);
    assert!(defs.contains_key("Bump"));
}
