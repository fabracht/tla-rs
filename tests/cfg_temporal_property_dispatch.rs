use tla_checker::ast::{Env, Expr, SafetyProperty};
use tla_checker::checker::{CheckResult, CheckerConfig};
use tla_checker::config::{apply_config, legacy_temporal_warning, parse_cfg};
use tla_checker::parser::parse;

fn apply(spec_src: &str, cfg_src: &str) -> (tla_checker::ast::Spec, Vec<String>) {
    let mut spec = parse(spec_src).expect("spec parses");
    let cfg = parse_cfg(cfg_src).expect("cfg parses");
    let mut domains = Env::new();
    let mut checker_config = CheckerConfig::default();
    let warnings = apply_config(
        &cfg,
        &mut spec,
        &mut domains,
        &mut checker_config,
        &[],
        &[],
        false,
    )
    .expect("apply_config ok");
    (spec, warnings)
}

#[test]
fn cfg_property_named_ending_in_spec_is_not_double_extracted() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        EventuallySpec == <>(x = 1)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY EventuallySpec\n";
    let (spec, _) = apply(spec_src, cfg_src);
    assert_eq!(
        spec.liveness_properties.len(),
        1,
        "a *Spec-named property is pre-extracted by the parser; the cfg path must not extract it again"
    );
}

#[test]
fn cfg_property_with_normal_name_is_extracted_once() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        Eventually1 == <>(x = 1)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY Eventually1\n";
    let (spec, _) = apply(spec_src, cfg_src);
    assert_eq!(spec.liveness_properties.len(), 1);
}

#[test]
fn cfg_existential_eventually_property_is_captured() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        S == 0..2\n\
        ExistsEventually == \\E i \\in S : <>(x = i)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY ExistsEventually\n";
    let (spec, _) = apply(spec_src, cfg_src);
    assert_eq!(spec.liveness_properties.len(), 1);
    assert!(
        matches!(
            &spec.liveness_properties[0].formula,
            Expr::Eventually(inner) if matches!(inner.as_ref(), Expr::Exists(_, _, _))
        ),
        "\\E i : <>Q(i) reduces to <>(\\E i : Q(i)); a \\E state predicate must land in liveness under <>"
    );
}

#[test]
fn cfg_unsupported_existential_temporal_property_is_a_config_error() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        S == 0..2\n\
        ExistsLeads == \\E i \\in S : (x = 0) ~> (x = i)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY ExistsLeads\n";
    let mut spec = parse(spec_src).expect("spec parses");
    let cfg = parse_cfg(cfg_src).expect("cfg parses");
    let result = apply_config(
        &cfg,
        &mut spec,
        &mut Env::new(),
        &mut CheckerConfig::default(),
        &[],
        &[],
        false,
    );
    let err = result.expect_err(
        "a property that cannot be checked must be rejected, not dropped and reported as satisfied",
    );
    assert!(
        err.contains("ExistsLeads") && err.contains("\\E"),
        "the error must name the property and the unsupported shape, got {err}"
    );
}

#[test]
fn cfg_stable_eventually_property_is_captured_not_dropped() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        StableEventually == <>[](x = 1)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY StableEventually\n";
    let (spec, warnings) = apply(spec_src, cfg_src);
    assert_eq!(
        spec.liveness_properties.len(),
        1,
        "<>[]P must be captured for checking, not silently dropped"
    );
    assert!(
        matches!(
            &spec.liveness_properties[0].formula,
            Expr::Eventually(inner) if matches!(inner.as_ref(), Expr::Always(_))
        ),
        "<>[]P must retain its Eventually(Always(..)) shape so the checker dispatches stable-eventually"
    );
    assert!(
        !warnings.iter().any(|w| w.contains("dropping")),
        "<>[]P must no longer warn about dropping its inner expression, got {warnings:?}"
    );
}

#[test]
fn cfg_universal_temporal_property_is_captured() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = x\n\
        S == 0..2\n\
        ForallEventually == \\A i \\in S : <>(x = i)\n\
        ====\n";
    let cfg_src = "INIT Init\nNEXT Next\nPROPERTY ForallEventually\n";
    let (spec, _) = apply(spec_src, cfg_src);
    assert_eq!(spec.liveness_properties.len(), 1);
    assert!(
        matches!(&spec.liveness_properties[0].formula, Expr::Forall(_, _, _)),
        "\\A i : <>Q(i) is kept whole and instantiated per element by the checker"
    );
    assert_eq!(
        spec.liveness_properties[0].name.as_ref(),
        "ForallEventually"
    );
}

fn run_existential_e2e(fair: bool) -> CheckResult {
    let dir = std::env::temp_dir().join("tla_cfg_exists_e2e");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("ExistsE2E.tla");
    let cfg_path = dir.join("ExistsE2E.cfg");
    let spec_line = if fair {
        "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Step)"
    } else {
        "Spec == Init /\\ [][Next]_vars"
    };
    let module = format!(
        "---- MODULE ExistsE2E ----\n\
         EXTENDS Naturals\n\
         VARIABLE x\n\
         vars == <<x>>\n\
         Init == x = 0\n\
         Step == x = 0 /\\ x' = 1\n\
         Next == Step \\/ UNCHANGED x\n\
         {spec_line}\n\
         TypeOK == x \\in 0..2\n\
         ExistsEventually == \\E i \\in {{1, 2}} : <>(x = i)\n\
         ====\n"
    );
    std::fs::write(&spec_path, module).unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\nINVARIANT TypeOK\nPROPERTY ExistsEventually\n",
    )
    .unwrap();

    let prepared = tla_checker::load::prepare_from_path(&spec_path, None, &[]).unwrap();
    let mut cc = prepared.checker_config;
    cc.check_liveness = true;
    let result = tla_checker::checker::check(&prepared.spec, &prepared.domains, &cc);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);
    result
}

#[test]
fn cfg_existential_eventually_is_checked_end_to_end() {
    match run_existential_e2e(true) {
        CheckResult::Ok(_) => {}
        other => panic!("WF forces x->1 so \\E i in {{1,2}} : <>(x=i) holds; got {other:?}"),
    }
    match run_existential_e2e(false) {
        CheckResult::LivenessViolation(_, _) => {}
        other => panic!(
            "without fairness x stalls at 0 so \\E i in {{1,2}} : <>(x=i) is violated; got {other:?}"
        ),
    }
}

#[test]
fn init_next_cfg_warns_when_it_discards_parsed_fairness() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 1 /\\ x' = x + 1\n\
        Nxt == Step \\/ UNCHANGED x\n\
        FairSpec == Init /\\ [][Nxt]_x /\\ WF_x(Step)\n\
        Reach == <>(x = 1)\n\
        ====\n";
    let (spec, warnings) = apply(spec_src, "INIT Init\nNEXT Nxt\nPROPERTY Reach\n");
    assert!(
        spec.fairness.is_empty(),
        "INIT/NEXT defines a behavior with no fairness, as in TLC"
    );
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("not applied") && w.contains("SPECIFICATION")),
        "discarding the module's fairness must be announced, got {warnings:?}"
    );
}

const CLASSIFY_MODULE: &str = "---- MODULE M ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    Init == x = 0\n\
    Step == x < 2 /\\ x' = x + 1\n\
    Next == Step \\/ UNCHANGED x\n\
    Spec == Init /\\ [][Next]_x /\\ WF_x(Step)\n\
    Mixed == x = 0 /\\ [](x < 5) /\\ [][x' >= x]_x /\\ <>(x = 2)\n\
    QInv == \\A i \\in {7, 8} : [](x # i)\n\
    ====\n";

#[test]
fn cfg_property_conjuncts_are_classified_like_tlc() {
    let (spec, _) = apply(CLASSIFY_MODULE, "SPECIFICATION Spec\nPROPERTY Mixed\n");
    let init: Vec<_> = spec
        .safety_properties
        .iter()
        .filter(|p| matches!(p, SafetyProperty::Init { .. }))
        .collect();
    let action: Vec<_> = spec
        .safety_properties
        .iter()
        .filter(
            |p| matches!(p, SafetyProperty::Action { formula: Expr::BoxAction(_, subscript), .. } if matches!(subscript.as_ref(), Expr::Var(v) if v.as_ref() == "x")),
        )
        .collect();
    assert_eq!(
        init.len(),
        1,
        "a state-level conjunct is checked on the initial states"
    );
    assert_eq!(action.len(), 1, "[][A]_x is an action property");
    assert!(
        spec.safety_properties
            .iter()
            .all(|p| p.name().as_ref() == "Mixed")
    );
    assert_eq!(
        spec.invariant_names.last().cloned().flatten().as_deref(),
        Some("Mixed"),
        "[](x < 5) is an implied invariant named after the property"
    );
    assert_eq!(spec.liveness_properties.len(), 1);
    assert_eq!(spec.liveness_properties[0].name.as_ref(), "Mixed");
    assert!(matches!(
        spec.liveness_properties[0].formula,
        Expr::Eventually(_)
    ));
}

#[test]
fn cfg_quantified_box_property_is_an_invariant() {
    let (spec, _) = apply(CLASSIFY_MODULE, "SPECIFICATION Spec\nPROPERTY QInv\n");
    assert!(spec.liveness_properties.is_empty());
    assert!(matches!(
        spec.invariants.last(),
        Some(Expr::Forall(_, _, _))
    ));
    assert_eq!(
        spec.invariant_names.last().cloned().flatten().as_deref(),
        Some("QInv")
    );
}

#[test]
fn specification_temporal_conjuncts_are_assumptions_not_properties() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 2 /\\ x' = x + 1\n\
        Next == Step \\/ UNCHANGED x\n\
        SpecA == Init /\\ [][Next]_x /\\ WF_x(Step) /\\ <>(x = 2)\n\
        Reach == <>(x = 1)\n\
        ====\n";
    let (spec, warnings) = apply(spec_src, "SPECIFICATION SpecA\nPROPERTY Reach\n");
    assert_eq!(
        spec.fairness.len(),
        1,
        "WF_x(Step) stays a fairness assumption"
    );
    assert_eq!(
        spec.liveness_properties
            .iter()
            .map(|p| p.name.as_ref())
            .collect::<Vec<_>>(),
        vec!["Reach"],
        "<>(x = 2) in SpecA is an assumption, never a property to check"
    );
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("SpecA") && w.contains("assumptions")),
        "an unenforced assumption must be announced, got {warnings:?}"
    );
}

#[test]
fn legacy_spec_temporal_formula_is_checked_with_a_deprecation_warning() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 2 /\\ x' = x + 1\n\
        Next == Step \\/ UNCHANGED x\n\
        Spec == Init /\\ [][Next]_x /\\ WF_x(Step) /\\ <>(x = 2)\n\
        ====\n";
    let spec = parse(spec_src).expect("spec parses");
    assert_eq!(spec.liveness_properties.len(), 1);
    assert!(spec.liveness_properties[0].from_specification);
    assert_eq!(spec.liveness_properties[0].name.as_ref(), "Spec");
    let warning = legacy_temporal_warning(&spec, true).expect("legacy mode is announced");
    assert!(warning.contains("Spec") && warning.contains("deprecated"));
    assert!(
        legacy_temporal_warning(&spec, false).is_none(),
        "without liveness checking the extracted formulas are unused"
    );
}

#[test]
fn legacy_spec_named_safety_property_is_still_checked() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x < 3 /\\ x' = x + 1\n\
        BoundSpec == [](x < 2)\n\
        ====\n";
    let (spec, _) = apply(spec_src, "PROPERTY BoundSpec\n");
    assert_eq!(
        spec.invariant_names.last().cloned().flatten().as_deref(),
        Some("BoundSpec"),
        "the parser extracts nothing from a *Spec safety property, so the cfg must classify it"
    );
}

#[test]
fn legacy_spec_named_liveness_property_is_extracted_once() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x < 3 /\\ x' = x + 1\n\
        ReachSpec == [](x < 5) /\\ <>(x = 3)\n\
        ====\n";
    let (spec, _) = apply(spec_src, "PROPERTY ReachSpec\n");
    assert_eq!(spec.liveness_properties.len(), 1);
    assert!(!spec.liveness_properties[0].from_specification);
    assert_eq!(
        spec.invariant_names.last().cloned().flatten().as_deref(),
        Some("ReachSpec")
    );
}

fn check_with_cfg(
    name: &str,
    module: &str,
    cfg: &str,
    configure: fn(&mut CheckerConfig),
) -> CheckResult {
    let dir = std::env::temp_dir().join(format!("tla_cfg_dispatch_{name}"));
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join(format!("{name}.tla"));
    std::fs::write(&spec_path, module).unwrap();
    std::fs::write(dir.join(format!("{name}.cfg")), cfg).unwrap();
    let prepared = tla_checker::load::prepare_from_path(&spec_path, None, &[]).unwrap();
    let mut cc = prepared.checker_config;
    configure(&mut cc);
    let result = tla_checker::checker::check(&prepared.spec, &prepared.domains, &cc);
    let _ = std::fs::remove_dir_all(&dir);
    result
}

const CONSTRAINED_MODULE: &str = "---- MODULE CONSTRAINED ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    Init == x = 0\n\
    Next == x < 3 /\\ x' = x + 1\n\
    Spec == Init /\\ [][Next]_x\n\
    Small == x < 2\n\
    Below2 == x < 2\n\
    Prop == [](x < 2)\n\
    ====\n";

#[test]
fn invariant_is_checked_on_a_state_outside_the_constraint() {
    let module = CONSTRAINED_MODULE.replace("CONSTRAINED", "ConInv");
    let result = check_with_cfg(
        "ConInv",
        &module,
        "SPECIFICATION Spec\nCONSTRAINT Small\nINVARIANT Below2\nCHECK_DEADLOCK FALSE\n",
        |_| {},
    );
    match result {
        CheckResult::InvariantViolation(cex, _) => {
            assert_eq!(
                cex.trace.len(),
                3,
                "0 -> 1 -> 2, where x = 2 is outside the constraint"
            )
        }
        other => panic!(
            "TLC checks invariants on states outside the CONSTRAINT and reports x = 2; got {other:?}"
        ),
    }
}

#[test]
fn continue_does_not_list_a_violated_property_as_checked() {
    let module = CONSTRAINED_MODULE.replace("CONSTRAINED", "ConCont");
    let result = check_with_cfg(
        "ConCont",
        &module,
        "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n",
        |cc| cc.continue_on_violation = true,
    );
    match result {
        CheckResult::Ok(stats) => {
            assert!(stats.violation_count > 0);
            assert!(
                stats.properties_checked.is_empty(),
                "a property with recorded violations is not reported as checked, got {:?}",
                stats.properties_checked
            );
        }
        other => panic!("--continue collects the [](x < 2) violations; got {other:?}"),
    }
}

#[test]
fn legacy_spec_named_property_rejects_what_it_cannot_check() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x < 3 /\\ x' = x + 1\n\
        LSpec == <>(x = 3) /\\ (x = 0 => <>(x = 9))\n\
        ====\n";
    let mut spec = parse(spec_src).expect("spec parses");
    let result = apply_config(
        &parse_cfg("PROPERTY LSpec\n").unwrap(),
        &mut spec,
        &mut Env::new(),
        &mut CheckerConfig::default(),
        &[],
        &[],
        false,
    );
    let err =
        result.expect_err("an unsupported conjunct must not be dropped and reported as checked");
    assert!(err.contains("LSpec"), "got {err}");
}

#[test]
fn legacy_spec_named_property_keeps_its_fairness_as_an_assumption() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 2 /\\ x' = x + 1\n\
        Next == Step \\/ UNCHANGED x\n\
        Spec == Init /\\ [][Next]_x /\\ WF_x(Step) /\\ <>(x = 2)\n\
        ====\n";
    let (spec, _) = apply(spec_src, "PROPERTY Spec\n");
    assert_eq!(
        spec.fairness.len(),
        1,
        "the parser applied WF_x(Step) as an assumption"
    );
    assert_eq!(spec.liveness_properties.len(), 1);
    assert!(!spec.liveness_properties[0].from_specification);
}

const REPEATED_MODULE: &str = "---- MODULE Repeated ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    Init == x = 0\n\
    Next == x < 8 /\\ x' = x + 1\n\
    Spec == Init /\\ [][Next]_x\n\
    P == [][x' # 3 /\\ x' # 7]_x /\\ [](x # 6) /\\ [](x # 9)\n\
    InvSmall == x < 20\n\
    ====\n";

#[test]
fn continue_records_every_action_property_violation() {
    let result = check_with_cfg(
        "Repeated",
        REPEATED_MODULE,
        "SPECIFICATION Spec\nPROPERTY P\nCHECK_DEADLOCK FALSE\n",
        |cc| cc.continue_on_violation = true,
    );
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(
                stats.violations_by_property,
                vec![(std::sync::Arc::from("P"), 2)],
                "TLC -continue reports both steps into x = 3 and x = 7"
            );
            assert_eq!(stats.violation_count, 3, "plus the [](x # 6) invariant");
            assert_eq!(stats.property_violation_traces.len(), 2);
        }
        other => panic!("--continue collects violations instead of stopping; got {other:?}"),
    }
}

#[test]
fn box_conjuncts_of_a_property_become_one_invariant() {
    let (spec, _) = apply(
        REPEATED_MODULE,
        "SPECIFICATION Spec\nINVARIANT InvSmall\nPROPERTY P\n",
    );
    let names: Vec<_> = spec
        .invariant_names
        .iter()
        .flatten()
        .map(|n| n.as_ref())
        .collect();
    assert_eq!(names, vec!["InvSmall", "P"]);
}

#[test]
fn name_detected_invariants_under_a_cfg_without_invariant_are_noted() {
    let (spec, warnings) = apply(REPEATED_MODULE, "SPECIFICATION Spec\n");
    assert_eq!(spec.invariants.len(), 1, "InvSmall is still checked");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("InvSmall") && w.contains("TLC would check none")),
        "got {warnings:?}"
    );
    let (_, listed) = apply(REPEATED_MODULE, "SPECIFICATION Spec\nINVARIANT InvSmall\n");
    assert!(!listed.iter().any(|w| w.contains("naming convention")));
}

#[test]
fn continue_json_reports_property_violations_when_no_invariant_failed() {
    let module = REPEATED_MODULE.replace("/\\ [](x # 6) /\\ [](x # 9)", "");
    let result = check_with_cfg(
        "RepeatedActions",
        &module.replace("MODULE Repeated", "MODULE RepeatedActions"),
        "SPECIFICATION Spec\nPROPERTY P\nINVARIANT InvSmall\nCHECK_DEADLOCK FALSE\n",
        |cc| cc.continue_on_violation = true,
    );
    let spec = tla_checker::parser::parse(&module).expect("spec parses");
    let json: serde_json::Value =
        serde_json::from_str(&tla_checker::checker::check_result_to_json(&result, &spec))
            .expect("valid JSON");
    assert_eq!(json["status"], "property_violation");
    assert_eq!(json["stats"]["violations_by_property"][0]["count"], 2);
}

#[test]
fn disjunction_with_a_non_liveness_disjunct_is_a_config_error() {
    let spec_src = "---- MODULE M ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = 1 - x\n\
        Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\n\
        StateOrLive == x = 1 \\/ <>(x = 1)\n\
        LiveOrLive == <>(x = 1) \\/ <>(x = 7)\n\
        ====\n";
    let mut spec = parse(spec_src).expect("spec parses");
    let err = apply_config(
        &parse_cfg("SPECIFICATION Spec\nPROPERTY StateOrLive\n").unwrap(),
        &mut spec,
        &mut Env::new(),
        &mut CheckerConfig::default(),
        &[],
        &[],
        false,
    )
    .expect_err("splitting x = 1 \\/ <>(x = 1) would report a violation TLC does not");
    assert!(
        err.contains("StateOrLive") && err.contains("disjunction"),
        "got {err}"
    );
    let (spec, _) = apply(spec_src, "SPECIFICATION Spec\nPROPERTY LiveOrLive\n");
    assert_eq!(
        spec.liveness_properties.len(),
        2,
        "a disjunction of liveness properties keeps the documented over-approximation"
    );
}

fn apply_with_engine(
    spec_src: &str,
    cfg_src: &str,
    engine: tla_checker::checker::LivenessEngine,
) -> (tla_checker::ast::Spec, Vec<String>) {
    let mut spec = parse(spec_src).expect("spec parses");
    let mut checker_config = CheckerConfig {
        liveness_engine: engine,
        ..CheckerConfig::default()
    };
    let warnings = apply_config(
        &parse_cfg(cfg_src).expect("cfg parses"),
        &mut spec,
        &mut Env::new(),
        &mut checker_config,
        &[],
        &[],
        false,
    )
    .expect("apply_config ok");
    (spec, warnings)
}

const SYNTACTIC_MODULE: &str = "---- MODULE M ----\n\
    EXTENDS Naturals\n\
    VARIABLE x\n\
    Init == x = 0\n\
    Step == x < 2 /\\ x' = x + 1\n\
    Next == Step \\/ UNCHANGED x\n\
    SpecA == Init /\\ [][Next]_x /\\ WF_x(Step) /\\ <>(x = 2)\n\
    NotEv == ~<>(x = 5)\n\
    StateOrLive == x = 1 \\/ <>(x = 1)\n\
    Mixed == x = 0 /\\ [](x < 5) /\\ [][x' >= x]_x /\\ <>(x = 2)\n\
    ====\n";

#[test]
fn tableau_engine_classifies_properties_on_their_syntax() {
    use tla_checker::checker::LivenessEngine::Tableau;
    let (spec, _) = apply_with_engine(
        SYNTACTIC_MODULE,
        "SPECIFICATION SpecA\nPROPERTY NotEv\n",
        Tableau,
    );
    assert!(
        spec.invariant_names
            .iter()
            .flatten()
            .all(|n| n.as_ref() != "NotEv")
    );
    assert_eq!(
        spec.liveness_properties.len(),
        1,
        "~<>P stays temporal, as in TLC"
    );
    assert!(matches!(spec.liveness_properties[0].formula, Expr::Not(_)));

    let (spec, _) = apply_with_engine(
        SYNTACTIC_MODULE,
        "SPECIFICATION SpecA\nPROPERTY StateOrLive\n",
        Tableau,
    );
    assert!(
        matches!(spec.liveness_properties[0].formula, Expr::Or(_, _)),
        "a disjunction with a temporal disjunct goes to the tableau whole"
    );

    let (spec, _) = apply_with_engine(
        SYNTACTIC_MODULE,
        "SPECIFICATION SpecA\nPROPERTY Mixed\n",
        Tableau,
    );
    assert_eq!(
        spec.safety_properties.len(),
        2,
        "the state predicate and [][A]_x"
    );
    assert_eq!(
        spec.invariant_names.last().cloned().flatten().as_deref(),
        Some("Mixed")
    );
    assert!(matches!(
        spec.liveness_properties[0].formula,
        Expr::Eventually(_)
    ));
}

#[test]
fn tableau_engine_keeps_specification_assumptions_without_a_warning() {
    use tla_checker::checker::LivenessEngine::{Legacy, Tableau};
    let cfg = "SPECIFICATION SpecA\nPROPERTY NotEv\n";
    let (spec, warnings) = apply_with_engine(SYNTACTIC_MODULE, cfg, Tableau);
    assert_eq!(
        spec.temporal_assumptions.len(),
        1,
        "<>(x = 2) is an assumption"
    );
    assert_eq!(spec.fairness.len(), 1);
    assert!(
        !warnings.iter().any(|w| w.contains("assumptions")),
        "the tableau engine enforces the assumption: {warnings:?}"
    );
    let (_, legacy_warnings) = apply_with_engine(SYNTACTIC_MODULE, cfg, Legacy);
    assert!(legacy_warnings.iter().any(|w| w.contains("assumptions")));
}

fn check_with_engine(name: &str, module: &str, cfg: Option<&str>) -> CheckResult {
    let dir = std::env::temp_dir().join(format!("tla_cfg_engine_{name}"));
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join(format!("{name}.tla"));
    std::fs::write(&spec_path, module).unwrap();
    if let Some(cfg) = cfg {
        std::fs::write(dir.join(format!("{name}.cfg")), cfg).unwrap();
    }
    let prepared = tla_checker::load::prepare_from_path_with_engine(
        &spec_path,
        None,
        &[],
        tla_checker::checker::LivenessEngine::Tableau,
    )
    .unwrap();
    let mut cc = prepared.checker_config;
    cc.check_liveness = true;
    cc.allow_deadlock = true;
    let result = tla_checker::checker::check(&prepared.spec, &prepared.domains, &cc);
    let _ = std::fs::remove_dir_all(&dir);
    result
}

#[test]
fn tableau_engine_accepts_builtin_operators_in_atoms() {
    let module = "---- MODULE Bits ----\n\
        EXTENDS Naturals, Bits\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 3 /\\ x' = x + 1\n\
        Next == Step \\/ UNCHANGED x\n\
        Spec == Init /\\ [][Next]_x /\\ WF_x(Step)\n\
        Ev == <>(BitAnd(x, 2) = 2)\n\
        ====\n";
    match check_with_engine(
        "Bits",
        module,
        Some("SPECIFICATION Spec\nPROPERTY Ev\nCHECK_DEADLOCK FALSE\n"),
    ) {
        CheckResult::Ok(_) => {}
        other => panic!("BitAnd is an ordinary state function; got {other:?}"),
    }
}

#[test]
fn tableau_engine_drops_fairness_from_legacy_spec_formulas() {
    let module = "---- MODULE Procs ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        P == {1, 2}\n\
        vars == <<x>>\n\
        Init == x = [p \\in P |-> 0]\n\
        A(p) == x[p] < 2 /\\ x' = [x EXCEPT ![p] = x[p] + 1]\n\
        Next == \\E p \\in P : A(p)\n\
        Spec == Init /\\ [][Next]_vars /\\ \\A p \\in P : (WF_vars(A(p)) /\\ <>(x[p] = 2))\n\
        ====\n";
    match check_with_engine("Procs", module, None) {
        CheckResult::Ok(stats) => assert_eq!(stats.states_explored, 9),
        other => panic!("each process is driven to 2 by its own WF; got {other:?}"),
    }
}
