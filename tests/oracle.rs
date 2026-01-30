use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use tlc_executor::ast::{Env, Value};
use tlc_executor::checker::{CheckResult, CheckerConfig, check};
use tlc_executor::parser::parse;

fn check_spec_file(path: &Path) -> CheckResult {
    check_spec_file_with_config(path, CheckerConfig::default())
}

fn check_spec_file_allow_deadlock(path: &Path) -> CheckResult {
    let mut config = CheckerConfig::default();
    config.allow_deadlock = true;
    check_spec_file_with_config(path, config)
}

fn check_spec_file_with_config(path: &Path, config: CheckerConfig) -> CheckResult {
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = match parse(&input) {
        Ok(s) => s,
        Err(e) => panic!("parse error in {}: {}", path.display(), e.message),
    };
    let domains = Env::new();
    check(&spec, &domains, &config)
}

fn try_parse_spec_file(path: &Path) -> Result<(), String> {
    let input = fs::read_to_string(path).expect("failed to read spec file");
    parse(&input).map(|_| ()).map_err(|e| e.message)
}

#[test]
fn test_should_pass_counter() {
    let path = Path::new("test_cases/should_pass/counter.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "counter.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_two_bit() {
    let path = Path::new("test_cases/should_pass/two_bit.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "two_bit.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_traffic_light() {
    let path = Path::new("test_cases/should_pass/traffic_light.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "traffic_light.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_violate_counter_overflow() {
    let path = Path::new("test_cases/should_violate/counter_overflow.tla");
    let result = check_spec_file(path);
    match result {
        CheckResult::InvariantViolation(cex, _) => {
            assert_eq!(cex.violated_invariant, 0);
            assert!(cex.trace.len() >= 6, "trace should reach count=6");
        }
        other => panic!(
            "counter_overflow.tla should violate invariant, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_should_violate_two_bit_overflow() {
    let path = Path::new("test_cases/should_violate/two_bit_overflow.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InvariantViolation(_, _)),
        "two_bit_overflow.tla should violate invariant, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_no_init() {
    let path = Path::new("test_cases/should_error/no_init.tla");
    let result = try_parse_spec_file(path);
    assert!(
        result.is_err() && result.as_ref().unwrap_err().contains("Init"),
        "no_init.tla should fail to parse with missing Init, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_no_next() {
    let path = Path::new("test_cases/should_error/no_next.tla");
    let result = try_parse_spec_file(path);
    assert!(
        result.is_err() && result.as_ref().unwrap_err().contains("Next"),
        "no_next.tla should fail to parse with missing Next, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_counter_with_constant() {
    let path = Path::new("test_cases/should_pass/counter_with_max.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("MAX"), Value::Int(5));

    let mut config = CheckerConfig::default();
    config.allow_deadlock = true;
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::Ok(_)),
        "counter_with_max.tla should pass with MAX=5, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_missing_constant() {
    let path = Path::new("test_cases/should_pass/counter_with_max.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let domains = Env::new();
    let config = CheckerConfig::default();
    let result = check(&spec, &domains, &config);

    match result {
        CheckResult::MissingConstants(missing) => {
            assert!(missing.iter().any(|c| c.as_ref() == "MAX"));
        }
        other => panic!("should report missing constant MAX, got: {:?}", other),
    }
}

#[test]
fn test_should_pass_let_in_next() {
    let path = Path::new("test_cases/should_pass/let_in_next.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "let_in_next.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_case_next() {
    let path = Path::new("test_cases/should_pass/case_next.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "case_next.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_if_then_else_next() {
    let path = Path::new("test_cases/should_pass/if_then_else_next.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "if_then_else_next.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_complex_next() {
    let path = Path::new("test_cases/should_pass/complex_next.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "complex_next.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_recursive_factorial() {
    let path = Path::new("test_cases/should_pass/recursive_factorial.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "recursive_factorial.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_exponentiation() {
    let path = Path::new("test_cases/should_pass/exponentiation.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "exponentiation.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_assume_constraint() {
    let path = Path::new("test_cases/should_pass/assume_constraint.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("N"), Value::Int(5));

    let mut config = CheckerConfig::default();
    config.allow_deadlock = true;
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::Ok(_)),
        "assume_constraint.tla with N=5 should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_fail_assume_constraint() {
    let path = Path::new("test_cases/should_pass/assume_constraint.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("N"), Value::Int(20));

    let config = CheckerConfig::default();
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::AssumeViolation(0)),
        "assume_constraint.tla with N=20 should violate ASSUME, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_proper_subset() {
    let path = Path::new("test_cases/should_pass/proper_subset.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "proper_subset.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_unicode_operators() {
    let path = Path::new("test_cases/should_pass/unicode_operators.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "unicode_operators.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_lambda() {
    let path = Path::new("test_cases/should_pass/lambda.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "lambda.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_boolean_set() {
    let path = Path::new("test_cases/should_pass/boolean_set.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "boolean_set.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_is_finite_set() {
    let path = Path::new("test_cases/should_pass/is_finite_set.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "is_finite_set.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_lazy_subset_membership() {
    let path = Path::new("test_cases/should_pass/lazy_subset.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "lazy_subset.tla should pass (SUBSET membership evaluated lazily), got: {:?}",
        result
    );
}

#[test]
fn test_symmetry_reduces_states() {
    let path = Path::new("test_cases/benchmark/symmetric_procs.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let proc_set: BTreeSet<Value> = ["p1", "p2", "p3"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut domains = Env::new();
    domains.insert(Arc::from("Proc"), Value::Set(proc_set));

    let config_no_sym = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    let result_no_sym = check(&spec, &domains, &config_no_sym);

    let config_sym = CheckerConfig {
        symmetric_constants: vec![Arc::from("Proc")],
        allow_deadlock: true,
        ..Default::default()
    };
    let result_sym = check(&spec, &domains, &config_sym);

    match (&result_no_sym, &result_sym) {
        (CheckResult::Ok(stats_no), CheckResult::Ok(stats_sym)) => {
            assert!(
                stats_sym.states_explored < stats_no.states_explored,
                "symmetry should reduce states: {} without, {} with",
                stats_no.states_explored,
                stats_sym.states_explored
            );
        }
        _ => panic!(
            "both should pass: no_sym={:?}, sym={:?}",
            result_no_sym, result_sym
        ),
    }
}

#[test]
fn test_should_pass_tlc_operators() {
    let path = Path::new("test_cases/should_pass/tlc_operators.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "tlc_operators.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_bags_operators() {
    let path = Path::new("test_cases/should_pass/bags_operators.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "bags_operators.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_official_twophase() {
    let path = Path::new("test_cases/official/TwoPhase.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let rm_set: BTreeSet<Value> = ["r1", "r2"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut domains = Env::new();
    domains.insert(Arc::from("RM"), Value::Set(rm_set));

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::Ok(_)),
        "TwoPhase.tla should pass, got: {:?}",
        result
    );
    assert!(
        !spec.invariants.is_empty(),
        "TwoPhase.tla should have TPTypeOK detected as invariant"
    );
}

#[test]
fn test_bitwise_and() {
    let path = Path::new("test_cases/should_pass/bitwise_and.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "bitwise_and.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_transitive_closure() {
    let path = Path::new("test_cases/should_pass/transitive_closure.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "transitive_closure.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_official_hanoi() {
    let path = Path::new("test_cases/official/Hanoi.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("D"), Value::Int(2));
    domains.insert(Arc::from("N"), Value::Int(3));

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::InvariantViolation { .. }),
        "Hanoi.tla should find solution (violate NotSolved), got: {:?}",
        result
    );
}

fn make_str_set(values: &[&str]) -> Value {
    let set: BTreeSet<Value> = values.iter().map(|s| Value::Str(Arc::from(*s))).collect();
    Value::Set(set)
}

fn make_int_set(values: &[i64]) -> Value {
    let set: BTreeSet<Value> = values.iter().map(|&n| Value::Int(n)).collect();
    Value::Set(set)
}

#[test]
fn test_mqdb_core() {
    let path = Path::new("test_cases/mqdb/MQDBCore.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("Ids"), make_str_set(&["id1"]));
    domains.insert(Arc::from("Values"), make_str_set(&["v1"]));
    domains.insert(Arc::from("MaxRetries"), Value::Int(2));
    domains.insert(Arc::from("MaxSeq"), Value::Int(3));

    let config = CheckerConfig {
        allow_deadlock: true,
        max_states: 5000,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(
            result,
            CheckResult::Ok(_) | CheckResult::MaxStatesExceeded(_)
        ),
        "MQDBCore.tla should pass or reach max states, got: {result:?}",
    );
}

#[test]
fn test_mqdb_constraints() {
    let path = Path::new("test_cases/mqdb/MQDBConstraints.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("Ids"), make_str_set(&["id1", "id2"]));
    domains.insert(Arc::from("Fields"), make_str_set(&["ref"]));
    domains.insert(Arc::from("FieldValues"), make_str_set(&["id1", "id2"]));

    let config = CheckerConfig {
        allow_deadlock: true,
        max_states: 50000,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(
            result,
            CheckResult::InvariantViolation(_, _)
                | CheckResult::Ok(_)
                | CheckResult::MaxStatesExceeded(_)
        ),
        "MQDBConstraints.tla should find violation, pass or reach max states, got: {result:?}",
    );
}

#[test]
fn test_mqdb_consumer_group() {
    let path = Path::new("test_cases/mqdb/MQDBConsumerGroup.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("Consumers"), make_str_set(&["c1", "c2"]));
    domains.insert(Arc::from("Groups"), make_str_set(&["g1"]));
    domains.insert(Arc::from("Partitions"), make_int_set(&[0, 1]));
    domains.insert(Arc::from("MaxTime"), Value::Int(3));
    domains.insert(Arc::from("HeartbeatTimeout"), Value::Int(2));

    let config = CheckerConfig {
        allow_deadlock: true,
        max_states: 5000,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(
            result,
            CheckResult::Ok(_) | CheckResult::MaxStatesExceeded(_)
        ),
        "MQDBConsumerGroup.tla should pass or reach max states, got: {result:?}",
    );
}

#[test]
fn test_mqdb_cluster() {
    let path = Path::new("test_cases/mqdb/MQDBCluster.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("Nodes"), make_str_set(&["n1", "n2"]));
    domains.insert(Arc::from("Partitions"), make_int_set(&[0]));
    domains.insert(Arc::from("MaxSeq"), Value::Int(1));

    let config = CheckerConfig {
        allow_deadlock: true,
        max_states: 500,
        max_depth: 200,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(
            result,
            CheckResult::InvariantViolation(_, _)
                | CheckResult::Ok(_)
                | CheckResult::MaxStatesExceeded(_)
                | CheckResult::MaxDepthExceeded(_)
        ),
        "MQDBCluster.tla should find violation, pass or reach limits, got: {result:?}",
    );
}

#[test]
fn test_should_error_no_initial_states() {
    let path = Path::new("test_cases/should_error/no_initial_states.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::NoInitialStates),
        "no_initial_states.tla should produce NoInitialStates, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_init_error() {
    let path = Path::new("test_cases/should_error/init_error.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InitError(_)),
        "init_error.tla should produce InitError, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_next_error() {
    let path = Path::new("test_cases/should_error/next_error.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::NextError(_, _)),
        "next_error.tla should produce NextError, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_invariant_error() {
    let path = Path::new("test_cases/should_error/invariant_error.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InvariantError(_, _)),
        "invariant_error.tla should produce InvariantError, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_deadlock() {
    let path = Path::new("test_cases/should_error/deadlock.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Deadlock(_, _, _)),
        "deadlock.tla should produce Deadlock, got: {:?}",
        result
    );
}
