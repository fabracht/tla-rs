use tla_checker::ast::Env;
use tla_checker::checker::{CheckResult, CheckerConfig, check};
use tla_checker::parser::parse;

/// `ENABLED` in the next-state relation is evaluated while states are generated,
/// as in TLC: `B` may only fire once `A` is disabled.
const SPEC: &str = r#"---- MODULE enabled_in_next ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
A == x < 2 /\ x' = x + 1 /\ y' = y
B == ~ENABLED A /\ y < 2 /\ y' = y + 1 /\ x' = x
Next == A \/ B
InvOrder == y > 0 => x = 2
===="#;

#[test]
fn enabled_guards_an_action_of_the_next_state_relation() {
    let spec = parse(SPEC).expect("spec parses");
    let config = CheckerConfig {
        allow_deadlock: true,
        quiet: true,
        ..CheckerConfig::default()
    };
    let result = check(&spec, &Env::new(), &config);
    let CheckResult::Ok(stats) = result else {
        panic!("expected a clean check, got {result:?}");
    };
    assert_eq!(stats.states_explored, 5);
}
