use tla_checker::ast::{Env, Expr};
use tla_checker::checker::{CheckResult, CheckerConfig};
use tla_checker::config::{apply_config, parse_cfg};
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
            &spec.liveness_properties[0],
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
            &spec.liveness_properties[0],
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
    assert!(!spec.quantified_temporal.is_empty());
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
