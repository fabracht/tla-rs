use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use tla_checker::ast::{Env, Value};
use tla_checker::checker::{CheckResult, CheckerConfig, PrepareSpecError, check};
use tla_checker::config::{apply_config, parse_cfg};
use tla_checker::parser::{parse, parse_with_warnings};

/// The suite runs under the walker by default; `TLA_ENGINE=inference` runs the
/// whole suite under the legacy engine so both can be exercised in CI.
fn inference_engine_selected() -> bool {
    std::env::var("TLA_ENGINE").ok().as_deref() == Some("inference")
}

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
    if inference_engine_selected() {
        config.use_inference_engine = true;
    }
    check_loaded(path, config)
}

/// Parse a spec (with its adjacent cfg) and check it under exactly the engine the
/// caller's config names — no `TLA_ENGINE` override. Used by the differential test
/// that must exercise both engines in one process.
fn check_loaded(path: &Path, mut config: CheckerConfig) -> CheckResult {
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

/// Differential corpus for the continuation-passing walker. Each of
/// these is a next-state relation where a primed variable's value depends on
/// another primed variable, an operator argument, an IF, or a chain — the shapes
/// the candidate-inference engine under-approximates into a silent false pass.
/// The walker must reach the violating successor. Asserted only under the walker
/// engine, since the inference engine reports these as passing.
#[test]
fn test_walker_dependent_next_state_probes() {
    if inference_engine_selected() {
        return;
    }
    for name in [
        "dep_assign",
        "reverse_order",
        "if_rhs",
        "disj_dep",
        "seq_index",
        "quant_wrap",
        "five_chain",
    ] {
        let path = format!("test_cases/walker/{name}.tla");
        let result = check_spec_file_allow_deadlock(Path::new(&path));
        assert!(
            matches!(result, CheckResult::InvariantViolation(_, _)),
            "{name}.tla must reach the violating successor under the walker, got: {result:?}"
        );
    }
}

/// Indexed-prime assignment is a *constraint* on a repeated key path, not an
/// overwrite. `f'[1] = 5 /\ f'[1] = 6` is unsatisfiable, and a `\A` that assigns
/// every index must not be silently overwritten by a later `f'[i] = e`. An
/// overwriting walker fabricates a successor satisfying neither conjunct. A
/// distinct-key assignment (`f'[1] = 5 /\ f'[2] = 6`, a tla-rs extension TLC does
/// not have) must still work. Asserted only under the walker engine.
#[test]
fn test_walker_indexed_prime_is_a_constraint() {
    if inference_engine_selected() {
        return;
    }
    for name in ["indexed_conflict", "indexed_forall_conflict"] {
        let path = format!("test_cases/walker/{name}.tla");
        let result = check_spec_file_allow_deadlock(Path::new(&path));
        assert!(
            matches!(result, CheckResult::Ok(_)),
            "{name}.tla: conflicting indexed assignments are unsatisfiable and must \
             yield no successor, got: {result:?}"
        );
    }
    let distinct =
        check_spec_file_allow_deadlock(Path::new("test_cases/walker/indexed_distinct.tla"));
    assert!(
        matches!(distinct, CheckResult::InvariantViolation(_, _)),
        "distinct indexed assignments must still combine into one successor, got: {distinct:?}"
    );
}

/// Cross-scope variable capture. A continuation conjunct (`z' = i`) pushed under
/// an outer `\E i` must keep seeing that `i` even when it is discharged inside an
/// operator body that rebinds `i` (`Pick(a) == \E i \in {5,6} : a = i`). With one
/// flat env and no scope journal the walker fabricates a bogus counterexample on
/// a valid spec. Both specs are valid — no violation exists — so this asserts the
/// walker does *not* report one. Asserted only under the walker engine.
#[test]
fn test_walker_no_cross_scope_capture() {
    if inference_engine_selected() {
        return;
    }
    for name in ["capture_scope", "capture_disjunct"] {
        let path = format!("test_cases/walker/{name}.tla");
        let result = check_spec_file_allow_deadlock(Path::new(&path));
        assert!(
            matches!(result, CheckResult::Ok(_)),
            "{name}.tla is valid; the walker must not fabricate a counterexample by \
             capturing a rebound quantifier variable, got: {result:?}"
        );
    }
}

/// `ENABLED A` is `\E vars' : A`, so an action that does not constrain every
/// variable is still enabled — a partial assignment is a legitimate witness.
/// Routed through the walker with a partial-assignment completion rule (the
/// state-generating rule would wrongly demand totality). Asserted only under the
/// walker engine.
#[test]
fn test_walker_enabled_partial_assignment() {
    if inference_engine_selected() {
        return;
    }
    let violated =
        check_spec_file_allow_deadlock(Path::new("test_cases/walker/enabled_partial.tla"));
    assert!(
        matches!(violated, CheckResult::InvariantViolation(_, _)),
        "ENABLED of an action that leaves a variable free must be true, got: {violated:?}"
    );
    let holds = check_spec_file_allow_deadlock(Path::new("test_cases/walker/enabled_holds.tla"));
    assert!(
        matches!(holds, CheckResult::Ok(_)),
        "ENABLED must still hold where the action is genuinely enabled, got: {holds:?}"
    );
}

/// Init-phase differential corpus. The candidate-inference init collector has no
/// arms for `\E`/`IF`/`LET`, so an initial state reached only through one of
/// those is silently dropped (a clean pass, or a bogus "no initial states").
/// The walker runs the same machine for Init as for Next. Asserted only under
/// the walker engine.
#[test]
fn test_walker_init_probes() {
    if inference_engine_selected() {
        return;
    }
    for name in ["init_disjunct", "init_exists", "init_if"] {
        let path = format!("test_cases/walker/{name}.tla");
        let result = check_spec_file_allow_deadlock(Path::new(&path));
        assert!(
            matches!(result, CheckResult::InvariantViolation(_, _)),
            "{name}.tla: the walker must reach the initial state the inference \
             collector drops, got: {result:?}"
        );
    }
}

/// A parameterized `LET` operator (`LET Double(n) == n * 2 IN Double(x) < 8`)
/// used in an invariant must resolve on both engines — the parser encodes it as a
/// `_params` marker that the evaluator now expands into a definition.
#[test]
fn test_should_violate_let_operator_invariant() {
    let path = Path::new("test_cases/should_violate/let_operator_invariant.tla");
    assert!(
        matches!(check_spec_file(path), CheckResult::InvariantViolation(..)),
        "let_operator_invariant.tla must resolve the parameterized LET operator and violate"
    );
}

/// A `LET`-local operator or value must shadow a same-named top-level
/// definition. `LET G(n) == 0 IN G(x)` with a top-level `G(n) == 1000` must use
/// the local `0`, not the top-level `1000`. The parser inlines operator
/// applications from the top-level definitions, so it must skip a name that an
/// enclosing `LET` binds. Covers both the parameterized and the zero-arg form.
#[test]
fn test_should_pass_let_shadows_toplevel() {
    let path = Path::new("test_cases/should_pass/let_shadows_toplevel.tla");
    assert!(
        matches!(check_spec_file_allow_deadlock(path), CheckResult::Ok(_)),
        "let_shadows_toplevel.tla: LET-local G/c (== 0) must shadow the top-level (== 1000)"
    );
}

/// The other direction: a `LET`-local operator whose body *causes* a violation
/// the top-level definition would not. `LET G(n) == 1000 IN G(x) < 50` with a
/// top-level `G(n) == 0` must violate — if the top-level `0` were used it would
/// be a false pass.
#[test]
fn test_should_violate_let_shadows_toplevel() {
    let path = Path::new("test_cases/should_violate/let_shadows_toplevel_violation.tla");
    assert!(
        matches!(check_spec_file(path), CheckResult::InvariantViolation(..)),
        "let_shadows_toplevel_violation.tla: the LET-local G (== 1000) must be used and violate"
    );
}

/// A parameterized `LET` operator in a next-state assignment
/// (`LET Bump(n) == n + 1 IN x' = Bump(x)`). The walker registers the operator as
/// a definition and enumerates the successor; the inference engine cannot infer a
/// candidate through the call, so this is asserted only under the walker.
#[test]
fn test_walker_let_operator_in_action() {
    if inference_engine_selected() {
        return;
    }
    let path = Path::new("test_cases/walker/let_operator_action.tla");
    assert!(
        matches!(
            check_spec_file_allow_deadlock(path),
            CheckResult::InvariantViolation(..)
        ),
        "the walker must enumerate `x' = Bump(x)` for a parameterized LET operator"
    );
}

/// An indexed assignment in Init with nothing to update — `Init == f[1] = 5`,
/// where `f` has no prior whole value and Init has no pre-state — cannot build
/// `f` and must be reported, not silently dropped. Dropping the branch is a
/// silent false pass when it is one disjunct of an otherwise-satisfiable Init.
/// Walker only; the legacy engine drops it silently.
#[test]
fn test_walker_init_indexed_without_base_is_loud() {
    if inference_engine_selected() {
        return;
    }
    let result =
        check_spec_file_allow_deadlock(Path::new("test_cases/walker/init_indexed_no_base.tla"));
    assert!(
        matches!(result, CheckResult::InitError(_)),
        "an indexed Init assignment with no base must be reported, got: {result:?}"
    );
}

/// Cliff guard: a wide prime-free guard (`\A i \in 1..24 : ...`) conjoined with a
/// single assignment. A structural walk of the guard branches on every inner
/// disjunct — O(2^24) dead work — before pruning. Hoisting prime-free conjuncts
/// evaluates the guard as one boolean instead, so the check finishes instantly.
/// Bound is generous to stay stable across machines while still catching a
/// return to exponential behaviour (which runs for minutes). Walker engine only.
#[test]
fn test_walker_hoists_prime_free_guard() {
    if inference_engine_selected() {
        return;
    }
    let start = std::time::Instant::now();
    let result = check_spec_file_allow_deadlock(Path::new("test_cases/walker/cliff_guard.tla"));
    let elapsed = start.elapsed();
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "cliff_guard.tla should pass, got: {result:?}"
    );
    assert!(
        elapsed.as_secs_f64() < 1.0,
        "cliff_guard.tla must not branch on the prime-free guard; took {elapsed:?}"
    );
}

/// The prime-free-guard hoist must still fire when the guard calls a recursive
/// operator (`Sum`). `contains_prime_ref` bails on the recursive cycle, and if it
/// bailed to "has a prime" the hoist would be skipped and the wide `\A` would
/// branch O(2^n). The recursive operator is prime-free, so the cycle contributes
/// no prime and the guard is hoisted. Walker only.
#[test]
fn test_walker_hoists_guard_with_recursive_operator() {
    if inference_engine_selected() {
        return;
    }
    let start = std::time::Instant::now();
    let result =
        check_spec_file_allow_deadlock(Path::new("test_cases/walker/cliff_guard_recursive.tla"));
    let elapsed = start.elapsed();
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "cliff_guard_recursive.tla should pass, got: {result:?}"
    );
    assert!(
        elapsed.as_secs_f64() < 1.0,
        "a prime-free guard calling a recursive operator must still hoist; took {elapsed:?}"
    );
}

/// A variable an action leaves unassigned is a malformed action: TLC raises a
/// hard error, and the inference engine silently drops the successor (a false
/// pass). The walker must fail loudly by default, and `--allow-unassigned-stutter`
/// must recover the lenient "unassigned means UNCHANGED" behaviour. Walker only.
#[test]
fn test_walker_unassigned_variable_is_loud() {
    if inference_engine_selected() {
        return;
    }
    let path = Path::new("test_cases/walker/unassigned_var.tla");

    let strict = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(strict, CheckResult::NextError(..)),
        "unassigned_var.tla must fail loudly when Bump leaves y unassigned, got: {strict:?}"
    );

    let lenient = check_spec_file_with_config(
        path,
        CheckerConfig {
            allow_deadlock: true,
            allow_unassigned_stutter: true,
            ..Default::default()
        },
    );
    assert!(
        matches!(lenient, CheckResult::Ok(_)),
        "--allow-unassigned-stutter must treat y as UNCHANGED, got: {lenient:?}"
    );
}

/// Indexed-prime membership `f'[k] \in S` enumerates the index over the set,
/// one successor per element — `f'[1] \in {5,6} /\ f'[2] = 0` reaches `[5,0]` and
/// `[6,0]`, so an invariant `f[1] # 5` is violated. The inference engine has no
/// arm for an indexed element and drops the successors (a clean pass, a false
/// pass); asserted only under the walker.
#[test]
fn test_walker_indexed_prime_membership() {
    if inference_engine_selected() {
        return;
    }
    let result = check_spec_file_allow_deadlock(Path::new("test_cases/walker/indexed_in.tla"));
    assert!(
        matches!(result, CheckResult::InvariantViolation(_, _)),
        "the walker must reach the successor `f'[1] \\in {{5,6}}` enumerates, got: {result:?}"
    );
}

/// A whole-variable prime assignment followed by an indexed reference to the
/// same variable is a *constraint* on the value already there, not an overwrite.
/// `f' = [i \in {1,2} |-> 9] /\ f'[1] = 5` is contradictory (`9 # 5`), so it has
/// no successor. The walker must not fabricate `[g EXCEPT ![1] = 5]`, which
/// satisfies the index but violates `f' = g` — a phantom successor and a false
/// pass. Both engines reach the same verdict here, so it is asserted on either.
#[test]
fn test_whole_assignment_then_index_is_a_constraint() {
    let result = check_spec_file(Path::new("test_cases/walker/whole_then_indexed.tla"));
    assert!(
        matches!(result, CheckResult::Deadlock(..)),
        "a whole assignment then a conflicting indexed constraint must yield no successor, \
         got: {result:?}"
    );
}

/// Engine-equivalence gate for the default flip. On well-formed specs the
/// inference engine handles correctly, the walker and the inference engine must
/// agree exactly: same reachable-state count, same transition count, and the same
/// per-action transition histogram (the "label histogram" — a stronger check than
/// the state count alone, since it pins which action produced each edge). Runs
/// both engines explicitly, so it is independent of `TLA_ENGINE`.
#[test]
fn test_engines_agree_on_known_correct_specs() {
    for name in [
        "official/TwoPhase",
        "should_pass/counter",
        "should_pass/two_bit",
    ] {
        let owned = format!("test_cases/{name}.tla");
        let path = Path::new(&owned);
        let cfg = |use_inference_engine| CheckerConfig {
            allow_deadlock: true,
            use_inference_engine,
            ..Default::default()
        };
        let walker = check_loaded(path, cfg(false));
        let infer = check_loaded(path, cfg(true));
        let (CheckResult::Ok(w), CheckResult::Ok(i)) = (&walker, &infer) else {
            panic!("{name}: both engines must complete; walker={walker:?} infer={infer:?}");
        };
        assert_eq!(
            w.states_explored, i.states_explored,
            "{name}: reachable-state count must match across engines"
        );
        assert_eq!(
            w.transitions, i.transitions,
            "{name}: transition count must match across engines"
        );
        assert_eq!(
            w.transitions_by_action, i.transitions_by_action,
            "{name}: per-action transition histogram must match across engines"
        );
    }
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
fn test_next_from_non_enumerable_set_is_an_error() {
    let path = Path::new("test_cases/should_error/next_not_enumerable.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::NextError(_, _, _)),
        "`x' \\in Seq({{1,2}})` cannot enumerate successors, so it must be reported; \
         discarding the enumeration error leaves no candidates, the collector falls back \
         to the current value, and the run reports a clean pass over one state, got: {:?}",
        result
    );
}

#[test]
fn test_init_from_non_enumerable_set_is_an_error() {
    let path = Path::new("test_cases/should_error/init_not_enumerable.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::InitError(_)),
        "a non-enumerable Init source must name itself, not surface as the misleading \
         `no initial states found`, got: {:?}",
        result
    );
}

#[test]
fn test_membership_as_a_check_is_not_a_candidate_source() {
    let path = Path::new("test_cases/should_pass/membership_check_not_source.tla");
    let result = check_spec_file_allow_deadlock(path);
    assert!(
        matches!(result, CheckResult::Ok(_)),
        "when another conjunct already determines the variable, `\\in` over a \
         non-enumerable set is only a membership test and must not be an error, got: {:?}",
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

/// Operator-argument capture. `Mutate(c, d)` is called with the `\E`-bound
/// variable `c`, whose name also binds inside the body (`{c \in S : c # author}`,
/// `[c \in S |-> ...]`). Inlining the operator must not capture: `c # author`
/// must stay `c # <the argument>`, not collapse to `c # c`. If it captures,
/// `recipients` is always empty, no pending diagram is ever produced, and the
/// reachable violation is missed — a false pass. Must violate on either engine.
#[test]
fn test_should_violate_operator_arg_capture() {
    let path = Path::new("test_cases/should_violate/operator_arg_capture.tla");
    assert!(
        matches!(check_spec_file(path), CheckResult::InvariantViolation(..)),
        "operator_arg_capture.tla must reach the violation; a captured argument hides it"
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
fn test_symmetry_cfg_directive_reduces_states() {
    // exercises the cfg `SYMMETRY Name` parse + apply path end to end, which the
    // check()-level symmetry tests bypass. Three symmetric procs each counting 0..2
    // give 27 states unreduced; symmetry collapses them to the 10 distinct multisets.
    let path = Path::new("test_cases/should_pass/symmetry_cfg.tla");
    match check_spec_file(path) {
        CheckResult::Ok(stats) => assert_eq!(
            stats.states_explored, 10,
            "cfg SYMMETRY must actually reduce the state space"
        ),
        other => panic!(
            "symmetry_cfg.tla should pass with reduction, got: {:?}",
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
    spec.invariants = vec![(*not_finished.1).clone()];
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

/// A parameterized-instance action in the next-state relation
/// (`Channel(id)!Send(msg)` under `\E id \in Ids`). The `WITH buffer <-
/// channels[id]` substitution places `id` under a prime, so resolving the
/// instance with `id` as a symbolic variable rather than its bound value makes
/// `prime_expr` produce an undefined `id'`. Both engines must reach the same 9
/// reachable states.
#[test]
fn test_parameterized_instance_in_next() {
    let path = Path::new("test_cases/should_pass/parameterized_instance.tla");
    match check_spec_file_allow_deadlock(path) {
        CheckResult::Ok(stats) => assert_eq!(
            stats.states_explored, 9,
            "parameterized_instance.tla should reach 9 states"
        ),
        other => panic!("parameterized_instance.tla should pass, got: {other:?}"),
    }
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
