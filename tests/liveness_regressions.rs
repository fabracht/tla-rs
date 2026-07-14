use std::path::{Path, PathBuf};

use tla_checker::checker::{CheckResult, check};
use tla_checker::load::prepare_from_path;

fn manifest_path(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)
}

fn check_liveness_at(path: &Path) -> CheckResult {
    let prepared = prepare_from_path(path, None, &[]).expect("spec prepares");
    let mut cc = prepared.checker_config;
    cc.check_liveness = true;
    check(&prepared.spec, &prepared.domains, &cc)
}

fn run_inline(name: &str, module: &str) -> CheckResult {
    let dir = std::env::temp_dir().join("tla_liveness_regressions");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join(format!("{name}.tla"));
    std::fs::write(&spec_path, module).unwrap();
    let prepared = prepare_from_path(&spec_path, None, &[]).expect("spec prepares");
    let mut cc = prepared.checker_config;
    cc.check_liveness = true;
    let result = check(&prepared.spec, &prepared.domains, &cc);
    let _ = std::fs::remove_file(&spec_path);
    result
}

// --- Standalone fixture wiring: these test_cases/ liveness specs were never
// exercised by cargo test, so a semantic regression in them went uncaught. ---

#[test]
fn fixture_eventually_holds_under_weak_fairness() {
    match check_liveness_at(&manifest_path("test_cases/should_pass/eventually_test.tla")) {
        CheckResult::Ok(_) => {}
        other => panic!("WF_x(Inc) must drive x to 5 so <>(x=5) holds; got {other:?}"),
    }
}

#[test]
fn fixture_infinitely_often_holds_under_weak_fairness() {
    match check_liveness_at(&manifest_path(
        "test_cases/should_pass/infinitely_often.tla",
    )) {
        CheckResult::Ok(_) => {}
        other => panic!("WF_x(Toggle) forces toggling forever so []<>(x=0) holds; got {other:?}"),
    }
}

#[test]
fn fixture_leads_to_holds_under_weak_fairness() {
    match check_liveness_at(&manifest_path("test_cases/should_pass/leads_to_test.tla")) {
        CheckResult::Ok(_) => {}
        other => panic!("WF_x(Inc) must drive x to 5 so (x=0)~>(x=5) holds; got {other:?}"),
    }
}

#[test]
fn fixture_eventually_violation_is_reported() {
    match check_liveness_at(&manifest_path(
        "test_cases/should_violate/liveness_violation.tla",
    )) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!("x only reaches 0/1, so <>(x=5) must be violated; got {other:?}"),
    }
}

#[test]
fn fixture_infinitely_often_violation_is_reported() {
    match check_liveness_at(&manifest_path(
        "test_cases/should_violate/infinitely_often_violation.tla",
    )) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!("x stutters at 3 forever, so []<>(x=0) must be violated; got {other:?}"),
    }
}

#[test]
fn fixture_leads_to_violation_is_reported() {
    match check_liveness_at(&manifest_path(
        "test_cases/should_violate/leads_to_violation.tla",
    )) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!("x never reaches 5, so (x=0)~>(x=5) must be violated; got {other:?}"),
    }
}

// --- Fix B: implicit stuttering. A machine with no explicit `\/ UNCHANGED` at
// the non-goal state can still stutter there forever under [][Next]_vars.
// Without fairness that stutter violates <>P; weak fairness rules it out. ---

const STUTTER_MODULE: &str = "---- MODULE ImplicitStutter ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    vars == <<x>>\n\
    Init == x = 0\n\
    Step == x = 0 /\\ x' = 1\n\
    Next == Step \\/ (x = 1 /\\ UNCHANGED x)\n\
    TypeOK == x \\in 0..1\n\
    SPEC_LINE\n\
    ====\n";

#[test]
fn implicit_stutter_without_fairness_violates_eventually() {
    let module =
        STUTTER_MODULE.replace("SPEC_LINE", "Spec == Init /\\ [][Next]_vars /\\ <>(x = 1)");
    match run_inline("ImplicitStutter", &module) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!(
            "x=0 has no explicit self-loop but [][Next]_vars still permits stuttering there \
             forever, so without fairness <>(x=1) must be violated; got {other:?}"
        ),
    }
}

#[test]
fn implicit_stutter_with_weak_fairness_holds() {
    let module = STUTTER_MODULE.replace(
        "SPEC_LINE",
        "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Step) /\\ <>(x = 1)",
    );
    match run_inline("ImplicitStutterFair", &module) {
        CheckResult::Ok(_) => {}
        other => panic!("WF_vars(Step) forbids stuttering at x=0, so <>(x=1) holds; got {other:?}"),
    }
}

// The stalled-consumer lesson: at the stuck state the only enabled transition is
// an UNFAIR action. The checker must not treat that action as forced.

const UNFAIR_ONLY_MODULE: &str = "---- MODULE UnfairOnly ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    vars == <<x>>\n\
    Init == x = 0\n\
    Rescue == x = 0 /\\ x' = 1\n\
    Next == Rescue \\/ (x = 1 /\\ UNCHANGED x)\n\
    TypeOK == x \\in 0..1\n\
    SPEC_LINE\n\
    ====\n";

#[test]
fn unfair_only_exit_does_not_rescue_liveness() {
    let module =
        UNFAIR_ONLY_MODULE.replace("SPEC_LINE", "Spec == Init /\\ [][Next]_vars /\\ <>(x = 1)");
    match run_inline("UnfairOnly", &module) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!(
            "the only exit from x=0 is the unfair Rescue action, so the checker must not \
             assume it is taken; <>(x=1) must be violated; got {other:?}"
        ),
    }
}

#[test]
fn fair_exit_rescues_liveness() {
    let module = UNFAIR_ONLY_MODULE.replace(
        "SPEC_LINE",
        "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Rescue) /\\ <>(x = 1)",
    );
    match run_inline("FairExit", &module) {
        CheckResult::Ok(_) => {}
        other => panic!("WF_vars(Rescue) forces the exit, so <>(x=1) holds; got {other:?}"),
    }
}

// --- Fix A: <>[]P (stable-eventually) is checked, not silently dropped. ---

#[test]
fn stable_eventually_holds_when_property_stabilizes() {
    let module = "---- MODULE StableHolds ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Step == x = 0 /\\ x' = 1\n\
        Next == Step \\/ (x = 1 /\\ UNCHANGED x)\n\
        TypeOK == x \\in 0..1\n\
        Spec == Init /\\ [][Next]_vars /\\ WF_vars(Step) /\\ <>[](x = 1)\n\
        ====\n";
    match run_inline("StableHolds", module) {
        CheckResult::Ok(_) => {}
        other => panic!("x reaches 1 and stays, so <>[](x=1) holds; got {other:?}"),
    }
}

#[test]
fn stable_eventually_violated_when_property_flips_forever() {
    let module = "---- MODULE StableFlips ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Toggle == x' = 1 - x\n\
        Next == Toggle\n\
        TypeOK == x \\in 0..1\n\
        Spec == Init /\\ [][Next]_vars /\\ WF_vars(Toggle) /\\ <>[](x = 1)\n\
        ====\n";
    match run_inline("StableFlips", module) {
        CheckResult::LivenessViolation(violation, _) => {
            assert!(
                violation.property.starts_with("<>[]"),
                "the reported property must be the stable-eventually form, got {}",
                violation.property
            );
        }
        other => panic!(
            "x toggles forever so x=1 never stabilizes; <>[](x=1) must be violated; got {other:?}"
        ),
    }
}

// --- #63: weak/strong fairness is defined on <<A>>_v = A /\ vars' # vars, so a
// stuttering step must never count as taking or enabling a fair action. ---

#[test]
fn weak_fairness_on_stutter_permitting_action_holds() {
    let module = "---- MODULE StutterFair ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Grow == x < 3 /\\ x' \\in {x, x + 1}\n\
        Next == Grow \\/ (x = 3 /\\ UNCHANGED x)\n\
        TypeOK == x \\in 0..3\n\
        Spec == Init /\\ [][Next]_vars /\\ WF_vars(Grow) /\\ <>(x = 3)\n\
        ====\n";
    match run_inline("StutterFair", module) {
        CheckResult::Ok(_) => {}
        other => panic!(
            "WF on <<Grow>>_vars (the x+1 step) forces x -> 3; the x'=x stutter must not be \
             counted as taking Grow, so <>(x=3) holds; got {other:?}"
        ),
    }
}

#[test]
fn vacuous_fairness_on_pure_stutter_action_does_not_rescue_liveness() {
    let module = "---- MODULE PureStutterFair ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Stay == x' = x\n\
        Move == x = 0 /\\ x' = 1\n\
        Next == Stay \\/ Move\n\
        TypeOK == x \\in 0..1\n\
        Spec == Init /\\ [][Next]_vars /\\ WF_vars(Stay) /\\ <>(x = 1)\n\
        ====\n";
    match run_inline("PureStutterFair", module) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!(
            "<<Stay>>_vars is never enabled (Stay only stutters), so WF_vars(Stay) is vacuous \
             and cannot force Move; <>(x=1) must be violated; got {other:?}"
        ),
    }
}

#[test]
fn strong_fairness_on_stutter_permitting_action_holds() {
    let module = "---- MODULE StutterStrongFair ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Grow == x < 3 /\\ x' \\in {x, x + 1}\n\
        Next == Grow \\/ (x = 3 /\\ UNCHANGED x)\n\
        TypeOK == x \\in 0..3\n\
        Spec == Init /\\ [][Next]_vars /\\ SF_vars(Grow) /\\ <>(x = 3)\n\
        ====\n";
    match run_inline("StutterStrongFair", module) {
        CheckResult::Ok(_) => {}
        other => panic!(
            "SF on <<Grow>>_vars (the x+1 step) is enabled infinitely often and forces x -> 3; \
             the x'=x stutter must not be counted as taking Grow, so <>(x=3) holds; got {other:?}"
        ),
    }
}

#[test]
fn vacuous_strong_fairness_on_pure_stutter_action_does_not_rescue_liveness() {
    let module = "---- MODULE PureStutterStrongFair ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        vars == <<x>>\n\
        Init == x = 0\n\
        Stay == x' = x\n\
        Move == x = 0 /\\ x' = 1\n\
        Next == Stay \\/ Move\n\
        TypeOK == x \\in 0..1\n\
        Spec == Init /\\ [][Next]_vars /\\ SF_vars(Stay) /\\ <>(x = 1)\n\
        ====\n";
    match run_inline("PureStutterStrongFair", module) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!(
            "<<Stay>>_vars is never enabled (Stay only stutters), so SF_vars(Stay) is vacuous \
             and cannot force Move; <>(x=1) must be violated; got {other:?}"
        ),
    }
}
