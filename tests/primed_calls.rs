use std::path::Path;

use tla_checker::checker::{CheckResult, check};
use tla_checker::load::prepare_from_path;

/// Priming a call the parser leaves uninlined (a `RECURSIVE` operator, an
/// `INSTANCE`'s operator) evaluates the whole call in the next state, as in TLC;
/// priming only its arguments read the operator's body in the current state.
fn check_with(cfg: &str) -> CheckResult {
    let dir = std::env::temp_dir().join(format!("tla_primed_calls_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let name: String = cfg
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let cfg_path = dir.join(format!("{name}.cfg"));
    std::fs::write(&cfg_path, cfg).expect("cfg written");
    let prepared = prepare_from_path(
        Path::new("test_cases/primed_calls/PrimedCalls.tla"),
        Some(&cfg_path),
        &[],
    )
    .expect("spec prepares");
    check(&prepared.spec, &prepared.domains, &prepared.checker_config)
}

fn property(name: &str) -> CheckResult {
    check_with(&format!(
        "SPECIFICATION Spec\nPROPERTY {name}\nCHECK_DEADLOCK FALSE\n"
    ))
}

#[test]
fn a_primed_recursive_call_reads_the_next_state() {
    assert!(matches!(property("RecOpPrimed"), CheckResult::Ok(_)));
    assert!(matches!(
        property("RecPrimedViolated"),
        CheckResult::PropertyViolation(..)
    ));
    assert!(matches!(property("SumPrimed"), CheckResult::Ok(_)));
}

#[test]
fn a_primed_instance_call_reads_the_next_state() {
    assert!(matches!(property("InstancePrimed"), CheckResult::Ok(_)));
    assert!(matches!(
        property("InstancePrimedViolated"),
        CheckResult::PropertyViolation(..)
    ));
}

#[test]
fn a_primed_call_in_the_next_state_relation_reads_the_successor() {
    let CheckResult::Ok(guard) = check_with("SPECIFICATION SpecGuard\nCHECK_DEADLOCK FALSE\n")
    else {
        panic!("Below(1)' as a guard");
    };
    assert_eq!(guard.states_explored, 2, "x' = 2 fails Below(1)'");
    let value = check_with("SPECIFICATION SpecValue\nINVARIANT InvYIsSum\nCHECK_DEADLOCK FALSE\n");
    assert!(
        matches!(value, CheckResult::Ok(_)),
        "y' = Sum(1)' is 1 + x': {value:?}"
    );
}
