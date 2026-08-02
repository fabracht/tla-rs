use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use tla_checker::ast::{Env, Value};
use tla_checker::checker::{CheckResult, CheckerConfig, PrepareSpecError, check};
use tla_checker::config::{apply_config, parse_cfg};
use tla_checker::parser::{parse, parse_with_warnings};

fn check_spec_file(path: &Path) -> CheckResult {
    check_spec_file_with_config(path, CheckerConfig::default())
}

fn check_spec_file_allow_deadlock(path: &Path) -> CheckResult {
    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    check_spec_file_with_config(path, config)
}

fn check_spec_file_with_config(path: &Path, mut config: CheckerConfig) -> CheckResult {
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let mut spec = match parse(&input) {
        Ok(s) => s,
        Err(e) => panic!("parse error in {}: {}", path.display(), e.message),
    };
    config.spec_path = Some(path.to_path_buf());
    let mut domains = Env::new();
    let cfg_path = path.with_extension("cfg");
    if cfg_path.exists() {
        let cfg_input = fs::read_to_string(&cfg_path).expect("failed to read cfg file");
        let tlc_cfg = parse_cfg(&cfg_input).expect("failed to parse cfg");
        apply_config(
            &tlc_cfg,
            &mut spec,
            &mut domains,
            &mut config,
            &[],
            &[],
            false,
        )
        .expect("failed to apply config");
    }
    check(&spec, &domains, &config)
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
fn test_should_pass_counter_instantiated() {
    let path = Path::new("test_cases/should_pass/counter_instance.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "counter_instance.tla should pass, got: {:?}",
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
fn test_membership_dispatch_is_shared() {
    let path = Path::new("test_cases/should_pass/membership_dispatch.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "nested structural sets must be decided the same way wherever `\\in` appears, \
         got: {:?}",
        result
    );
}

#[test]
fn test_membership_in_invariant_uses_shared_dispatch() {
    let path = Path::new("test_cases/should_pass/membership_in_invariant.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "invariants are evaluated by the context evaluator, which had its own weaker \
         copy of `\\in` — a bare invariant over SUBSET/Seq/[f: S]/[D -> R] is what \
         exercises that path, got: {:?}",
        result
    );
}

#[test]
fn test_model_value_does_not_shadow_a_definition() {
    let path = Path::new("test_cases/should_violate/model_value_shadowing.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InvariantViolation(_, _)),
        "a model value named the same as an operator must not be bound over it — the \
         environment is consulted before definitions, so binding `Threshold` as a model \
         value makes `x < Threshold` compare against an atom and the run stops early, \
         got: {:?}",
        result
    );
}

#[test]
fn test_undefined_name_in_set_domain_is_reported() {
    let path = Path::new("test_cases/should_error/undefined_in_seq_domain.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::InvariantError(_, _, _)),
        "an undefined name in a `Seq(..)` domain must be reported even when the sequence \
         is empty; deferring the domain evaluation into the element loop makes the \
         invariant silently vacuous, got: {:?}",
        result
    );
}

#[test]
fn test_function_canonicality() {
    let path = Path::new("test_cases/should_pass/function_canonicality.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "every construct that builds a function must yield the canonical layout for its \
         domain: `f = [i \\in DOMAIN f |-> f[i]]` must hold for all of them, and equal \
         functions must collapse to one set element, got: {:?}",
        result
    );
}

#[test]
fn test_multi_update_except_threads_accumulated_result() {
    let path = Path::new("test_cases/should_pass/except_sequence.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "[f EXCEPT ![a] = e1, ![b] = e2] means [[f EXCEPT ![a] = e1] EXCEPT ![b] = e2], \
         so `@` in a later update sees the earlier updates, got: {:?}",
        result
    );
}

#[test]
fn test_model_value_conformance() {
    let path = Path::new("test_cases/should_pass/model_value_conformance.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "model-value semantics pinned to an actual TLC 2.19 run: a model value is never \
         equal to a same-named string, and a function over model values is not a record, \
         got: {:?}",
        result
    );
}

#[test]
fn test_tlc_conformance_functions() {
    let path = Path::new("test_cases/should_pass/tlc_conformance_functions.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "every invariant here is one probe from a differential corpus whose expected \
         answer was taken from an actual TLC 2.19 run; 31 of the 55 were wrong before \
         records, sequences and functions were unified, got: {:?}",
        result
    );
}

#[test]
fn test_function_identity_matches_tlc() {
    let path = Path::new("test_cases/should_pass/function_identity.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "a record, a sequence and the same function written with `:>` denote ONE value: \
         they must compare equal, dedup to one set element, and be interchangeable in \
         `[S -> T]`, `[f: T]`, witness search, field access and sequence operators, \
         got: {:?}",
        result
    );
}

#[test]
fn test_model_values_are_distinct_from_strings() {
    let path = Path::new("test_cases/should_pass/model_values_distinct.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "a model value must never equal a same-named string, got: {:?}",
        result
    );
}

#[test]
fn test_model_values_do_not_collapse_state_space() {
    let path = Path::new("test_cases/should_pass/model_value_state_space.tla");
    let result = check_spec_file(path);
    match result {
        CheckResult::Ok(stats) => assert_eq!(
            stats.states_explored, 16,
            "{{n1, \"n1\", n2, \"n2\"}} has 4 distinct members, so the powerset reached \
             is 16 states; conflating model values with strings collapses it to 4 and \
             silently skips reachable states"
        ),
        other => panic!("model_value_state_space.tla should pass, got: {:?}", other),
    }
}

#[test]
fn test_should_pass_except_sequence() {
    let path = Path::new("test_cases/should_pass/except_sequence.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "EXCEPT must work on sequences, including nested paths through \
         records and sequences in both directions, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_fn_merge_precedence() {
    let path = Path::new("test_cases/should_pass/fn_merge_precedence.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "`:>` binds tighter than `@@` but looser than `+` and `..`, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_record_as_function() {
    let path = Path::new("test_cases/should_pass/record_as_function.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "record_as_function.tla should pass (records are functions from field names), got: {:?}",
        result
    );
}

#[test]
fn test_negation_in_precedence() {
    let path = Path::new("test_cases/should_pass/negation_in.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "negation_in.tla should pass (~x \\in S parses as ~(x \\in S)), got: {:?}",
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
fn test_should_violate_tuple_indexed_prime() {
    let path = Path::new("test_cases/should_violate/tuple_indexed_prime.tla");
    let result = check_spec_file_allow_deadlock(path);
    match result {
        CheckResult::InvariantViolation(cex, _) => {
            assert_eq!(cex.violated_invariant, 0);
        }
        other => panic!(
            "x'[1] = 5 must infer the successor <<5, 2>> and violate Inv; \
             a 0-based tuple index here yields no transitions and a false pass, got: {:?}",
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
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InitError(_)),
        "no_init.tla should produce InitError for missing Init, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_no_next() {
    let path = Path::new("test_cases/should_error/no_next.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::NextError(..)),
        "no_next.tla should produce NextError for missing Next, got: {:?}",
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

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
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
        CheckResult::PrepareError(PrepareSpecError::MissingConstants(missing)) => {
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
fn test_should_pass_recursive_in_next() {
    let path = Path::new("test_cases/should_pass/recursive_in_next.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "recursive_in_next.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_recursive_dotdot() {
    let path = Path::new("test_cases/should_pass/recursive_dotdot.tla");
    let result = check_spec_file(path);
    match &result {
        CheckResult::Ok(stats) => assert_eq!(stats.states_explored, 2),
        _ => panic!("recursive_dotdot.tla should pass, got: {:?}", result),
    }
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

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
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
        matches!(
            result,
            CheckResult::PrepareError(PrepareSpecError::AssumeViolation(0))
        ),
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
fn test_record_set_membership() {
    let path = Path::new("test_cases/should_pass/record_set_membership.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "record_set_membership.tla should pass (structural membership in [f: T] \
         record-type sets with an infinite Seq(T) field, via \\in / \\notin / \\subseteq), got: {:?}",
        result
    );
}

#[test]
fn test_symmetry_rejects_non_model_values() {
    let path = Path::new("test_cases/benchmark/symmetric_procs.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let proc_set: BTreeSet<Value> = ["p1", "p2", "p3"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut domains = Env::new();
    domains.insert(Arc::from("Proc"), Value::set(proc_set));

    let config = CheckerConfig {
        symmetric_constants: vec![Arc::from("Proc")],
        allow_deadlock: true,
        ..Default::default()
    };

    match check(&spec, &domains, &config) {
        CheckResult::PrepareError(PrepareSpecError::NonModelValueSymmetry(name, members)) => {
            assert_eq!(name.as_ref(), "Proc");
            assert_eq!(members.len(), 3);
        }
        other => panic!(
            "symmetry over a set of strings is unsound — it requires uninterpreted, \
             pairwise-distinct elements — and must be rejected, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_symmetry_reduces_states() {
    let path = Path::new("test_cases/benchmark/symmetric_procs.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let proc_set: BTreeSet<Value> = ["p1", "p2", "p3"]
        .iter()
        .map(|s| Value::Model(Arc::from(*s)))
        .collect();

    let mut domains = Env::new();
    domains.insert(Arc::from("Proc"), Value::set(proc_set));

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
fn test_should_pass_tuple_binding_quantifier() {
    let path = Path::new("test_cases/should_pass/tuple_binding_quantifier.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "tuple_binding_quantifier.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_tuple_binding_comprehension() {
    let path = Path::new("test_cases/should_pass/tuple_binding_comprehension.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "tuple_binding_comprehension.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_duplicate_tuple_binder() {
    let input = r#"---- MODULE dup ----
VARIABLE x
Pairs == {<<1, 2>>}
Init == x = 0
Next == \E <<a, a>> \in Pairs : x' = a
===="#;
    let (_, warnings) = parse_with_warnings(input).expect("spec should parse with warning");
    assert!(
        warnings.iter().any(|w| w.value.contains("duplicate name")),
        "expected duplicate-name warning, got: {:?}",
        warnings.iter().map(|w| &w.value).collect::<Vec<_>>()
    );
}

#[test]
fn test_should_pass_unbounded_choose() {
    let path = Path::new("test_cases/should_pass/unbounded_choose.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "unbounded_choose.tla should pass, got: {:?}",
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
    domains.insert(Arc::from("RM"), Value::set(rm_set));

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

#[test]
fn test_official_queens() {
    let path = Path::new("test_cases/official/Queens.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse Queens.tla");

    let mut domains = Env::new();
    domains.insert(Arc::from("N"), Value::Int(4));

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::Ok(_)),
        "Queens.tla with N=4 should pass, got: {result:?}",
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
        matches!(result, CheckResult::NextError(..)),
        "next_error.tla should produce NextError, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_invariant_error() {
    let path = Path::new("test_cases/should_error/invariant_error.tla");
    let result = check_spec_file(path);
    assert!(
        matches!(result, CheckResult::InvariantError(..)),
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

#[test]
fn test_should_pass_pingpong() {
    let path = Path::new("test_cases/should_pass/pingpong.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("NumberOfClients"), Value::Int(1));
    domains.insert(Arc::from("NumberOfPings"), Value::Int(1));

    let mut config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    config.spec_path = Some(path.to_path_buf());
    let result = check(&spec, &domains, &config);

    assert!(
        matches!(result, CheckResult::Ok(_)),
        "pingpong.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_pingpong_action_labels_not_unnamed() {
    let path = Path::new("test_cases/should_pass/pingpong.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let mut spec = parse(&input).expect("failed to parse spec");

    let mut domains = Env::new();
    domains.insert(Arc::from("NumberOfClients"), Value::Int(2));
    domains.insert(Arc::from("NumberOfPings"), Value::Int(2));

    let not_finished = spec
        .definitions
        .get(&Arc::from("NotFinished") as &str)
        .expect("NotFinished should be defined")
        .clone();
    spec.invariants = vec![not_finished.1];
    spec.invariant_names = vec![Some(Arc::from("NotFinished"))];

    let mut config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    config.spec_path = Some(path.to_path_buf());
    let result = check(&spec, &domains, &config);

    match result {
        CheckResult::InvariantViolation(cex, _stats) => {
            let unnamed_count = cex.actions.iter().filter(|a| a.is_none()).count();
            let named: Vec<_> = cex
                .actions
                .iter()
                .filter_map(|a| a.as_ref().map(|s| s.as_ref()))
                .collect();
            assert!(
                !named.is_empty(),
                "trace should have at least one named action"
            );
            assert_eq!(
                unnamed_count,
                1,
                "only the initial state should have no action label, but got {} unnamed out of {} total; named: {:?}",
                unnamed_count,
                cex.actions.len(),
                named
            );
        }
        other => panic!(
            "pingpong with NotFinished invariant should violate, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_cfg_twophase_auto_load() {
    let path = Path::new("test_cases/official/TwoPhase.tla");
    let cfg_path = Path::new("test_cases/official/TwoPhase.cfg");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let cfg_input = fs::read_to_string(cfg_path).expect("failed to read cfg file");
    let mut spec = parse(&input).expect("failed to parse spec");
    let tlc_cfg = parse_cfg(&cfg_input).expect("failed to parse cfg");

    let mut domains = Env::new();
    let mut config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    config.spec_path = Some(path.to_path_buf());

    apply_config(
        &tlc_cfg,
        &mut spec,
        &mut domains,
        &mut config,
        &[],
        &[],
        false,
    )
    .expect("failed to apply config");

    assert!(
        domains.contains_key(&Arc::from("RM")),
        "RM should be set from cfg"
    );

    let result = check(&spec, &domains, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(
                stats.states_explored, 288,
                "3 RMs should produce 288 states"
            );
        }
        other => panic!("TwoPhase with cfg should pass, got: {:?}", other),
    }
}

#[test]
fn test_should_pass_inline_disjunction() {
    let path = Path::new("test_cases/should_pass/inline_disjunction.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "inline_disjunction.tla should pass, got: {result:?}",
    );
}

#[test]
fn test_should_pass_specification_directive() {
    let path = Path::new("test_cases/should_pass/specification_directive.tla");
    let cfg_path = Path::new("test_cases/should_pass/specification_directive.cfg");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let cfg_input = fs::read_to_string(cfg_path).expect("failed to read cfg file");
    let mut spec = parse(&input).expect("failed to parse spec");
    let tlc_cfg = parse_cfg(&cfg_input).expect("failed to parse cfg");

    let mut domains = Env::new();
    let mut config = CheckerConfig {
        spec_path: Some(path.to_path_buf()),
        ..Default::default()
    };

    apply_config(
        &tlc_cfg,
        &mut spec,
        &mut domains,
        &mut config,
        &[],
        &[],
        false,
    )
    .expect("failed to apply config");

    let result = check(&spec, &domains, &config);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "specification_directive.tla with SPECIFICATION directive should pass, got: {result:?}",
    );
}

#[test]
fn test_should_pass_specification_directive_multi_var() {
    let path = Path::new("test_cases/should_pass/specification_directive_multi_var.tla");
    let cfg_path = Path::new("test_cases/should_pass/specification_directive_multi_var.cfg");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let cfg_input = fs::read_to_string(cfg_path).expect("failed to read cfg file");
    let mut spec = parse(&input).expect("failed to parse spec");
    let tlc_cfg = parse_cfg(&cfg_input).expect("failed to parse cfg");

    let mut domains = Env::new();
    let mut config = CheckerConfig {
        spec_path: Some(path.to_path_buf()),
        ..Default::default()
    };

    apply_config(
        &tlc_cfg,
        &mut spec,
        &mut domains,
        &mut config,
        &[],
        &[],
        false,
    )
    .expect("failed to apply config");

    let result = check(&spec, &domains, &config);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "specification_directive_multi_var.tla with SPECIFICATION directive should pass, got: {result:?}",
    );
    if let CheckResult::Ok(stats) = &result {
        assert_eq!(stats.states_explored, 4);
        assert_eq!(stats.transitions, 8);
    }
}

#[test]
fn test_cfg_cli_constant_overrides_cfg() {
    let path = Path::new("test_cases/official/TwoPhase.tla");
    let cfg_input = "CONSTANT RM = {rm1, rm2, rm3}\nINIT TPInit\nNEXT TPNext\nINVARIANT TPTypeOK";
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let mut spec = parse(&input).expect("failed to parse spec");
    let tlc_cfg = parse_cfg(cfg_input).expect("failed to parse cfg");

    let mut rm_set = BTreeSet::new();
    rm_set.insert(Value::Str("r1".into()));
    rm_set.insert(Value::Str("r2".into()));
    let cli_constants = vec![(Arc::from("RM"), Value::set(rm_set))];

    let mut domains = Env::new();
    let mut config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    config.spec_path = Some(path.to_path_buf());

    apply_config(
        &tlc_cfg,
        &mut spec,
        &mut domains,
        &mut config,
        &cli_constants,
        &[],
        false,
    )
    .expect("failed to apply config");

    for (name, val) in &cli_constants {
        domains.insert(name.clone(), val.clone());
    }

    let result = check(&spec, &domains, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 56, "2 RMs should produce 56 states");
        }
        other => panic!("TwoPhase with CLI override should pass, got: {:?}", other),
    }
}

#[test]
fn test_should_error_extends_missing_module() {
    let path = Path::new("test_cases/should_error/extends_missing_module.tla");
    let result = check_spec_file(path);
    match result {
        CheckResult::PrepareError(PrepareSpecError::InstanceError(e)) => {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("NotThere"),
                "error should mention missing module name, got: {}",
                msg
            );
        }
        other => panic!(
            "extends_missing_module.tla should produce PrepareSpecError::InstanceError, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_should_pass_extends_file_module() {
    let path = Path::new("test_cases/should_pass/extends_file_module/extends_file_module.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "extends_file_module.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_extends_transitive() {
    let path = Path::new("test_cases/should_pass/extends_transitive/extends_transitive.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "extends_transitive.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_pass_extends_override() {
    let path = Path::new("test_cases/should_pass/extends_override/extends_override.tla");
    let result = check_spec_file_allow_deadlock(path);
    match &result {
        CheckResult::Ok(stats) => {
            assert_eq!(
                stats.states_explored, 4,
                "spec Limit=3 should produce 4 states (0,1,2,3)"
            );
        }
        other => panic!("extends_override.tla should pass, got: {:?}", other),
    }
}

#[test]
fn test_should_pass_extends_multiple() {
    let path = Path::new("test_cases/should_pass/extends_multiple/extends_multiple.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "extends_multiple.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_should_error_extends_parse_error() {
    let path = Path::new("test_cases/should_error/extends_parse_error/extends_parse_error.tla");
    let result = check_spec_file(path);
    match result {
        CheckResult::PrepareError(PrepareSpecError::InstanceError(e)) => {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("Broken"),
                "error should mention the broken module name, got: {}",
                msg
            );
        }
        other => panic!(
            "extends_parse_error.tla should produce PrepareSpecError::InstanceError, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_should_error_extends_cycle() {
    let path = Path::new("test_cases/should_error/extends_cycle/extends_cycle.tla");
    let result = check_spec_file_allow_deadlock(path);
    match result {
        CheckResult::PrepareError(PrepareSpecError::InstanceError(e)) => {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("cyclic"),
                "error should mention cyclic dependency, got: {}",
                msg
            );
        }
        other => panic!(
            "extends_cycle.tla should produce PrepareSpecError::InstanceError, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_constant_override_user_wins() {
    let path = Path::new("test_cases/should_pass/constant_override.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("failed to parse spec");

    let mut custom_set = BTreeSet::new();
    custom_set.insert(Value::Str("a".into()));
    custom_set.insert(Value::Str("b".into()));
    custom_set.insert(Value::Str("c".into()));

    let mut domains = Env::new();
    domains.insert(Arc::from("BOOLEAN"), Value::set(custom_set));

    let config = CheckerConfig {
        allow_deadlock: true,
        ..Default::default()
    };
    let result = check(&spec, &domains, &config);

    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(
                stats.states_explored, 3,
                "BOOLEAN overridden to {{a,b,c}} should produce 3 states, got {}",
                stats.states_explored
            );
        }
        other => panic!(
            "constant_override.tla with BOOLEAN={{a,b,c}} should pass, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_parameterized_instance_in_init() {
    let path = Path::new("test_cases/should_pass/param_instance_init.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "param_instance_init.tla should pass, got: {:?}",
        result
    );
}

#[test]
fn test_parameterized_instance_init_unbound_var() {
    let path = Path::new("test_cases/should_pass/param_instance_init_unbound.tla");
    let result = check_spec_file_allow_deadlock(path);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(
                stats.states_explored, 1,
                "should find exactly 1 initial state"
            );
        }
        other => panic!("param_instance_init_unbound.tla should pass, got: {other:?}"),
    }
}

#[test]
fn test_parameterized_inv_prefix_not_misclassified() {
    let path = Path::new("test_cases/should_pass/parameterized_inv_prefix.tla");
    let input = fs::read_to_string(path).expect("failed to read spec file");
    let spec = parse(&input).expect("parse should succeed");
    assert_eq!(
        spec.invariants.len(),
        1,
        "only zero-arg InvCounter should be auto-detected, not InvokeAction/InitNode/NextStep"
    );
    assert_eq!(spec.invariant_names[0].as_deref(), Some("InvCounter"));
}

fn run_with_large_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");
}

#[test]
fn test_should_pass_fr_list() {
    run_with_large_stack(|| {
        let path = Path::new("test_cases/should_pass/FRList.tla");
        let result = check_spec_file_allow_deadlock(path);
        assert!(
            matches!(result, CheckResult::Ok(_)),
            "FRList.tla should pass all structural invariants, got: {result:?}"
        );
    });
}

#[test]
fn test_should_pass_fr_list_lin() {
    run_with_large_stack(|| {
        let path = Path::new("test_cases/should_pass/FRListLin.tla");
        let result = check_spec_file_allow_deadlock(path);
        assert!(
            matches!(result, CheckResult::Ok(_)),
            "FRListLin.tla should pass linearizability + structural invariants, got: {result:?}"
        );
    });
}
