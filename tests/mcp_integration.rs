use std::collections::BTreeMap;
use std::path::PathBuf;

use serde_json::json;
use tla_checker::mcp::runner;
use tla_checker::mcp::schema::{
    AppendBeatInput, CheckOutcome, CheckSpecInput, DemoStatus, ErrorPhase, ExportDemoDocInput,
    ExportDemoHtmlInput, LimitKind, ListInvariantsInput, ReplayScenarioInput, ScenarioStatus,
    ValidateDemoInput, ValidateSpecInput, ValidationStatus,
};

fn pass_spec(name: &str) -> String {
    format!("test_cases/should_pass/{}.tla", name)
}

fn violate_spec(name: &str) -> String {
    format!("test_cases/should_violate/{}.tla", name)
}

#[test]
fn validate_spec_returns_summary_for_valid_spec() {
    let input = ValidateSpecInput {
        spec_path: pass_spec("base_counter"),
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        config_path: None,
    };
    let out = runner::validate_spec(&input);
    assert_eq!(out.schema_version, "1");
    assert!(matches!(out.status, ValidationStatus::Ok));
    let spec = out.spec.expect("spec summary present on Ok");
    assert_eq!(spec.vars, vec!["x".to_string()]);
    assert!(spec.has_init);
    assert!(spec.has_next);
    assert!(
        spec.invariants
            .iter()
            .any(|i| i.name.as_deref() == Some("InvBounded"))
    );
}

#[test]
fn validate_spec_reports_io_error_for_missing_file() {
    let input = ValidateSpecInput {
        spec_path: "does_not_exist.tla".into(),
        constants: BTreeMap::new(),
        config_path: None,
    };
    let out = runner::validate_spec(&input);
    assert!(matches!(out.status, ValidationStatus::Error));
    let err = out.error.expect("error present");
    let body = serde_json::to_value(&err).unwrap();
    assert_eq!(body["kind"], json!("io"));
    assert!(
        body["message"]
            .as_str()
            .unwrap()
            .contains("does_not_exist.tla")
    );
}

#[test]
fn list_invariants_returns_invariant_names() {
    let input = ListInvariantsInput {
        spec_path: pass_spec("base_counter"),
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        config_path: None,
    };
    let out = runner::list_invariants(&input);
    assert_eq!(out.schema_version, "1");
    assert!(matches!(out.status, ValidationStatus::Ok));
    assert_eq!(out.invariants.len(), 1);
    assert_eq!(out.invariants[0].name.as_deref(), Some("InvBounded"));
}

#[test]
fn check_spec_returns_invariant_violation_with_trace() {
    let input = CheckSpecInput {
        spec_path: violate_spec("counter_overflow"),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    assert_eq!(out.schema_version, "1");
    match out.outcome {
        CheckOutcome::InvariantViolation {
            invariant,
            trace,
            actions,
            stats,
        } => {
            assert_eq!(invariant.as_deref(), Some("Inv"));
            assert!(!trace.is_empty());
            assert_eq!(trace.len(), actions.len());
            let first = trace.first().unwrap();
            let val = first.vars.get("count").expect("count var present");
            assert_eq!(val.display, "0");
            assert_eq!(val.json, json!(0));
            assert!(stats.states_explored > 0);
        }
        other => panic!("expected invariant_violation, got {:?}", other),
    }
}

#[test]
fn check_spec_reports_limit_reached_when_budget_exhausted() {
    let input = CheckSpecInput {
        spec_path: violate_spec("counter_overflow"),
        max_states: 2,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    match out.outcome {
        CheckOutcome::LimitReached { limit, stats } => {
            assert!(matches!(limit, LimitKind::MaxStates));
            assert!(stats.states_explored >= 2);
        }
        other => panic!("expected limit_reached, got {:?}", other),
    }
}

#[test]
fn check_spec_reports_missing_constant_as_structured_error() {
    let input = CheckSpecInput {
        spec_path: pass_spec("base_counter"),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    match out.outcome {
        CheckOutcome::Error { phase, error, .. } => {
            assert!(matches!(phase, ErrorPhase::Constant));
            assert!(error.message.contains("start_val"));
        }
        other => panic!("expected error, got {:?}", other),
    }
}

#[test]
fn check_spec_reports_parse_error_with_span() {
    let path = std::env::temp_dir().join("tla_mcp_bad_spec.tla");
    std::fs::write(&path, "this is not a tla spec at all\n").unwrap();
    let input = CheckSpecInput {
        spec_path: path.to_string_lossy().into_owned(),
        max_states: 10,
        max_depth: 10,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&path);
    match out.outcome {
        CheckOutcome::Error { phase, .. } => {
            assert!(matches!(phase, ErrorPhase::Parse));
        }
        other => panic!("expected parse error, got {:?}", other),
    }
}

#[test]
fn check_spec_passes_for_safe_spec() {
    let input = CheckSpecInput {
        spec_path: pass_spec("base_counter"),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        symmetry: None,
        allow_deadlock: Some(true),
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    match out.outcome {
        CheckOutcome::Ok { .. } | CheckOutcome::InvariantViolation { .. } => {}
        other => panic!("expected ok or violation, got {:?}", other),
    }
}

#[test]
fn check_spec_honors_cfg_check_deadlock_false_when_input_unset() {
    let dir = std::env::temp_dir().join("tla_mcp_cfg_deadlock");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Stuck.tla");
    let cfg_path = dir.join("Stuck.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE Stuck ----\nVARIABLE x\nInit == x = 0\nNext == x = 1 /\\ x' = 2\n====\n",
    )
    .unwrap();
    std::fs::write(&cfg_path, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n").unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 10,
        max_depth: 10,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    assert!(
        matches!(out.outcome, CheckOutcome::Ok { .. }),
        "cfg CHECK_DEADLOCK FALSE should make deadlock acceptable; got {:?}",
        out.outcome
    );
}

#[test]
fn check_spec_reports_deadlock_by_default_when_neither_cfg_nor_input_allows() {
    let dir = std::env::temp_dir().join("tla_mcp_no_cfg_deadlock");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Stuck2.tla");
    std::fs::write(
        &spec_path,
        "---- MODULE Stuck2 ----\nVARIABLE x\nInit == x = 0\nNext == x = 1 /\\ x' = 2\n====\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 10,
        max_depth: 10,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_dir(&dir);

    assert!(
        matches!(out.outcome, CheckOutcome::Deadlock { .. }),
        "with no cfg and allow_deadlock unset, deadlock should be reported; got {:?}",
        out.outcome
    );
}

#[test]
fn validate_spec_surfaces_parser_warnings() {
    let path = std::env::temp_dir().join("tla_mcp_warn_spec.tla");
    std::fs::write(
        &path,
        "---- MODULE WarnSpec ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nBadOp ==\n====\n",
    )
    .unwrap();
    let input = ValidateSpecInput {
        spec_path: path.to_string_lossy().into_owned(),
        constants: BTreeMap::new(),
        config_path: None,
    };
    let out = runner::validate_spec(&input);
    let _ = std::fs::remove_file(&path);

    assert!(matches!(out.status, ValidationStatus::Ok));
    assert!(
        !out.warnings.is_empty(),
        "expected parser warning for malformed BadOp body; got none"
    );
    assert!(
        out.warnings.iter().any(|w| w.message.contains("BadOp")),
        "warning should mention BadOp; got {:?}",
        out.warnings
    );
}

#[test]
fn replay_scenario_returns_step_by_step_trace() {
    let input = ReplayScenarioInput {
        spec_path: pass_spec("base_counter"),
        scenario: "step: x' = 1\nstep: x' = 2\n".to_string(),
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        config_path: None,
    };
    let out = runner::replay_scenario(&input);
    assert_eq!(out.schema_version, "1");
    assert!(
        matches!(out.status, ScenarioStatus::Ok),
        "expected ok, got {:?}",
        out.status
    );
    assert_eq!(out.trace.len(), 3, "initial state + 2 steps");
    assert_eq!(out.trace[0].step_index, None);
    assert_eq!(out.trace[1].step_index, Some(0));
    assert_eq!(out.trace[2].step_index, Some(1));
    let first = &out.trace[0].state;
    assert_eq!(first.vars.get("x").unwrap().display, "0");
    let last = &out.trace[2].state;
    assert_eq!(last.vars.get("x").unwrap().display, "2");
}

#[test]
fn replay_scenario_reports_failure_with_available_actions() {
    let input = ReplayScenarioInput {
        spec_path: pass_spec("base_counter"),
        scenario: "step: x' = 42\n".to_string(),
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        config_path: None,
    };
    let out = runner::replay_scenario(&input);
    assert!(
        matches!(out.status, ScenarioStatus::Failed),
        "expected failed, got {:?}",
        out.status
    );
    let failure = out.failure.expect("failure info present");
    assert_eq!(failure.step_index, 0);
    assert!(!failure.available_actions.is_empty());
}

#[test]
fn check_spec_honors_cfg_constraint_directive() {
    let dir = std::env::temp_dir().join("tla_mcp_cfg_constraint");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Counter.tla");
    let cfg_path = dir.join("Counter.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE Counter ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nBounded == x < 5\n====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "INIT Init\nNEXT Next\nCONSTRAINT Bounded\nCHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { stats } => {
            assert_eq!(
                stats.states_explored, 5,
                "Bounded constraint should cap at 5 states (x=0..4); got {}",
                stats.states_explored
            );
        }
        other => panic!("expected ok with bounded state space, got {:?}", other),
    }
}

#[test]
fn check_spec_honors_input_state_constraint() {
    let dir = std::env::temp_dir().join("tla_mcp_input_constraint");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Counter2.tla");
    std::fs::write(
        &spec_path,
        "---- MODULE Counter2 ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: Some(true),
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: Some("x < 3".to_string()),
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { stats } => {
            assert_eq!(
                stats.states_explored, 3,
                "x<3 should cap at 3 states (x=0,1,2); got {}",
                stats.states_explored
            );
        }
        other => panic!("expected ok with bounded state space, got {:?}", other),
    }
}

#[test]
fn check_spec_reports_state_constraint_parse_error() {
    let input = CheckSpecInput {
        spec_path: pass_spec("base_counter"),
        max_states: 10,
        max_depth: 10,
        max_seconds: 30,
        constants: [("start_val".to_string(), "0".to_string())]
            .into_iter()
            .collect(),
        symmetry: None,
        allow_deadlock: Some(true),
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: Some(")))".to_string()),
        config_path: None,
    };
    let out = runner::check_spec(&input);
    match out.outcome {
        CheckOutcome::Error { phase, error, .. } => {
            assert!(matches!(phase, ErrorPhase::Config));
            assert!(error.message.contains("state_constraint"));
        }
        other => panic!(
            "expected config error for bad state_constraint, got {:?}",
            other
        ),
    }
}

#[test]
fn check_spec_extracts_wf_from_non_spec_named_specification() {
    let dir = std::env::temp_dir().join("tla_mcp_wf_progress");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Progress.tla");
    let cfg_path = dir.join("Progress.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE Progress ----\n\
         VARIABLE x\n\
         Init == x = 0\n\
         Step == x' = x + 1 /\\ x < 3\n\
         vars == <<x>>\n\
         ProgressFormula == Init /\\ [][Step]_vars /\\ WF_vars(Step)\n\
         EventuallyDone == <>(x = 3)\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION ProgressFormula\n\
         PROPERTY EventuallyDone\n\
         CHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { .. } => {}
        CheckOutcome::Error { ref error, .. } if error.message.contains("WF") => {
            panic!(
                "WF_vars leaked into eval path — extraction did not run for non-*Spec named SPECIFICATION; got {:?}",
                out.outcome
            );
        }
        other => panic!("expected ok, got {:?}", other),
    }
}

#[test]
fn check_spec_handles_wf_in_spec_named_definition() {
    let dir = std::env::temp_dir().join("tla_mcp_wf_spec_named");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("WithSpec.tla");
    let cfg_path = dir.join("WithSpec.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE WithSpec ----\n\
         VARIABLE x\n\
         Init == x = 0\n\
         Step == x' = x + 1 /\\ x < 3\n\
         vars == <<x>>\n\
         Spec == Init /\\ [][Step]_vars /\\ WF_vars(Step)\n\
         EventuallyDone == <>(x = 3)\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\n\
         PROPERTY EventuallyDone\n\
         CHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { .. } => {}
        other => panic!(
            "expected ok for *Spec named SPECIFICATION with WF, got {:?}",
            other
        ),
    }
}

#[test]
fn check_spec_detects_leads_to_violation_in_sub_scc() {
    let dir = std::env::temp_dir().join("tla_mcp_leads_to_sub_scc");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("RwStarve.tla");
    let cfg_path = dir.join("RwStarve.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE RwStarve ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxReaders\n\
         VARIABLES readers, writer, writerWaiting\n\
         vars == << readers, writer, writerWaiting >>\n\
         Init == readers = 0 /\\ writer = \"none\" /\\ writerWaiting = FALSE\n\
         ReaderArrive  == writer = \"none\" /\\ readers + 1 <= MaxReaders\n\
                       /\\ readers' = readers + 1 /\\ UNCHANGED <<writer, writerWaiting>>\n\
         ReaderLeave   == readers > 0 /\\ readers' = readers - 1\n\
                       /\\ UNCHANGED <<writer, writerWaiting>>\n\
         WriterRequest == ~writerWaiting /\\ writer = \"none\"\n\
                       /\\ writerWaiting' = TRUE /\\ UNCHANGED <<readers, writer>>\n\
         WriterAcquire == writerWaiting /\\ readers = 0 /\\ writer = \"none\"\n\
                       /\\ writer' = \"active\" /\\ writerWaiting' = FALSE /\\ UNCHANGED readers\n\
         WriterRelease == writer = \"active\" /\\ writer' = \"none\"\n\
                       /\\ UNCHANGED <<readers, writerWaiting>>\n\
         Next == ReaderArrive \\/ ReaderLeave \\/ WriterRequest \\/ WriterAcquire \\/ WriterRelease\n\
         Spec == Init /\\ [][Next]_vars /\\ WF_vars(ReaderLeave) /\\ WF_vars(WriterAcquire)\n\
         Live == writerWaiting ~> writer = \"active\"\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\nCONSTANT MaxReaders = 2\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::LivenessViolation {
            property,
            prefix,
            cycle,
            ..
        } => {
            assert!(
                property.contains("LeadsTo") || property.contains("~>"),
                "expected leads-to property, got {}",
                property
            );
            assert!(!prefix.is_empty() || !cycle.is_empty());
        }
        other => panic!(
            "expected liveness_violation for starvation cycle, got {:?}",
            other
        ),
    }
}

#[test]
fn check_spec_does_not_report_leads_to_violation_when_subscc_unreachable() {
    let dir = std::env::temp_dir().join("tla_mcp_leads_to_fixed");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("RwFixed.tla");
    let cfg_path = dir.join("RwFixed.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE RwFixed ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxReaders\n\
         VARIABLES readers, writer, writerWaiting\n\
         vars == << readers, writer, writerWaiting >>\n\
         Init == readers = 0 /\\ writer = \"none\" /\\ writerWaiting = FALSE\n\
         ReaderArrive  == writer = \"none\" /\\ ~writerWaiting /\\ readers + 1 <= MaxReaders\n\
                       /\\ readers' = readers + 1 /\\ UNCHANGED <<writer, writerWaiting>>\n\
         ReaderLeave   == readers > 0 /\\ readers' = readers - 1\n\
                       /\\ UNCHANGED <<writer, writerWaiting>>\n\
         WriterRequest == ~writerWaiting /\\ writer = \"none\"\n\
                       /\\ writerWaiting' = TRUE /\\ UNCHANGED <<readers, writer>>\n\
         WriterAcquire == writerWaiting /\\ readers = 0 /\\ writer = \"none\"\n\
                       /\\ writer' = \"active\" /\\ writerWaiting' = FALSE /\\ UNCHANGED readers\n\
         WriterRelease == writer = \"active\" /\\ writer' = \"none\"\n\
                       /\\ UNCHANGED <<readers, writerWaiting>>\n\
         Next == ReaderArrive \\/ ReaderLeave \\/ WriterRequest \\/ WriterAcquire \\/ WriterRelease\n\
         Spec == Init /\\ [][Next]_vars /\\ WF_vars(ReaderLeave) /\\ WF_vars(WriterAcquire)\n\
         Live == writerWaiting ~> writer = \"active\"\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\nCONSTANT MaxReaders = 2\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { .. } => {}
        other => panic!(
            "fixed rwlock spec should satisfy leads-to (no !Q sub-cycle reachable from P-state via !Q transitions); got {:?}",
            other
        ),
    }
}

#[test]
fn validate_spec_surfaces_resolved_constants() {
    let input = ValidateSpecInput {
        spec_path: pass_spec("base_counter"),
        constants: [("start_val".to_string(), "42".to_string())]
            .into_iter()
            .collect(),
        config_path: None,
    };
    let out = runner::validate_spec(&input);
    assert!(matches!(out.status, ValidationStatus::Ok));
    let summary = out.spec.expect("summary present");
    assert_eq!(summary.constants.len(), 1);
    let binding = &summary.constants[0];
    assert_eq!(binding.name, "start_val");
    let value = binding.value.as_ref().expect("value resolved");
    assert_eq!(value.display, "42");
    assert_eq!(value.json, json!(42));
}

#[test]
fn validate_spec_lists_unbound_constants_with_no_value() {
    let input = ValidateSpecInput {
        spec_path: pass_spec("base_counter"),
        constants: BTreeMap::new(),
        config_path: None,
    };
    let out = runner::validate_spec(&input);
    let summary = out.spec.expect("summary present");
    assert_eq!(summary.constants.len(), 1);
    assert_eq!(summary.constants[0].name, "start_val");
    assert!(
        summary.constants[0].value.is_none(),
        "unbound constant should have value: None"
    );
}

#[test]
fn check_spec_reports_max_seconds_when_time_budget_exhausted() {
    let dir = std::env::temp_dir().join("tla_mcp_max_seconds");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("Big.tla");
    std::fs::write(
        &spec_path,
        "---- MODULE Big ----\n\
         EXTENDS Naturals\n\
         CONSTANT N\n\
         VARIABLE x\n\
         Init == x = 0\n\
         Next == x' = (x + 1) % N\n\
         ====\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 1_000_000,
        max_depth: 1_000_000,
        max_seconds: 0,
        constants: [("N".to_string(), "100".to_string())].into_iter().collect(),
        symmetry: None,
        allow_deadlock: Some(true),
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::LimitReached { limit, stats } => {
            assert!(
                matches!(limit, LimitKind::MaxSeconds),
                "expected MaxSeconds limit, got {:?}",
                limit
            );
            assert!(
                stats.elapsed_secs >= 0.0,
                "stats should include elapsed time"
            );
        }
        other => panic!(
            "max_seconds=0 must always fire on the first BFS iteration; got {:?}",
            other
        ),
    }
}

#[test]
fn check_spec_reports_max_seconds_when_liveness_phase_runs_with_zero_budget() {
    let dir = std::env::temp_dir().join("tla_mcp_max_seconds_liveness");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("LivenessBudget.tla");
    let cfg_path = dir.join("LivenessBudget.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE LivenessBudget ----\n\
         EXTENDS Naturals\n\
         VARIABLE x\n\
         vars == << x >>\n\
         Init == x = 0\n\
         Step == x' = (x + 1) % 3\n\
         Next == Step\n\
         Spec == Init /\\ [][Next]_vars /\\ WF_vars(Step)\n\
         EventuallyDone == <>(x = 2)\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\nPROPERTY EventuallyDone\nCHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 1_000_000,
        max_depth: 1_000_000,
        max_seconds: 0,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::LimitReached { limit, .. } => {
            assert!(
                matches!(limit, LimitKind::MaxSeconds),
                "expected MaxSeconds, got {:?}",
                limit
            );
        }
        other => panic!(
            "max_seconds=0 with check_liveness must return LimitReached regardless of which phase fires the check; got {:?}",
            other
        ),
    }
}

#[test]
fn check_spec_leads_to_violation_cycle_contains_state_where_p_holds() {
    let dir = std::env::temp_dir().join("tla_mcp_leads_to_cycle_p");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("RwStarve2.tla");
    let cfg_path = dir.join("RwStarve2.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE RwStarve2 ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxReaders\n\
         VARIABLES readers, writer, writerWaiting\n\
         vars == << readers, writer, writerWaiting >>\n\
         Init == readers = 0 /\\ writer = \"none\" /\\ writerWaiting = FALSE\n\
         ReaderArrive  == writer = \"none\" /\\ readers + 1 <= MaxReaders\n\
                       /\\ readers' = readers + 1 /\\ UNCHANGED <<writer, writerWaiting>>\n\
         ReaderLeave   == readers > 0 /\\ readers' = readers - 1\n\
                       /\\ UNCHANGED <<writer, writerWaiting>>\n\
         WriterRequest == ~writerWaiting /\\ writer = \"none\"\n\
                       /\\ writerWaiting' = TRUE /\\ UNCHANGED <<readers, writer>>\n\
         WriterAcquire == writerWaiting /\\ readers = 0 /\\ writer = \"none\"\n\
                       /\\ writer' = \"active\" /\\ writerWaiting' = FALSE /\\ UNCHANGED readers\n\
         WriterRelease == writer = \"active\" /\\ writer' = \"none\"\n\
                       /\\ UNCHANGED <<readers, writerWaiting>>\n\
         Next == ReaderArrive \\/ ReaderLeave \\/ WriterRequest \\/ WriterAcquire \\/ WriterRelease\n\
         Spec == Init /\\ [][Next]_vars /\\ WF_vars(ReaderLeave) /\\ WF_vars(WriterAcquire)\n\
         Live == writerWaiting ~> writer = \"active\"\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(
        &cfg_path,
        "SPECIFICATION Spec\nCONSTANT MaxReaders = 2\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n",
    )
    .unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 100,
        max_depth: 50,
        max_seconds: 30,
        constants: BTreeMap::new(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: Some(true),
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::LivenessViolation { cycle, prefix, .. } => {
            let cycle_has_p = cycle.iter().any(|s| {
                s.vars
                    .get("writerWaiting")
                    .map(|v| v.json == json!(true))
                    .unwrap_or(false)
            });
            assert!(
                cycle_has_p,
                "leads-to violation cycle must contain at least one P-state (writerWaiting=TRUE) — reported cycle was {:?}",
                cycle
            );
            assert!(
                !prefix.is_empty(),
                "prefix should describe how the cycle is reached"
            );
        }
        other => panic!("expected liveness_violation, got {:?}", other),
    }
}

#[test]
fn check_spec_cli_constants_override_cfg_constants() {
    let dir = std::env::temp_dir().join("tla_mcp_cli_overrides_cfg");
    std::fs::create_dir_all(&dir).unwrap();
    let spec_path = dir.join("BoundedCounter.tla");
    let cfg_path = dir.join("BoundedCounter.cfg");
    std::fs::write(
        &spec_path,
        "---- MODULE BoundedCounter ----\n\
         EXTENDS Naturals\n\
         CONSTANT Cap\n\
         VARIABLE x\n\
         Init == x = 0\n\
         Next == x' = x + 1 /\\ x' < Cap\n\
         ====\n",
    )
    .unwrap();
    std::fs::write(&cfg_path, "CONSTANT Cap = 5\nCHECK_DEADLOCK FALSE\n").unwrap();

    let input = CheckSpecInput {
        spec_path: spec_path.to_string_lossy().into_owned(),
        max_states: 1000,
        max_depth: 100,
        max_seconds: 30,
        constants: [("Cap".to_string(), "10".to_string())]
            .into_iter()
            .collect(),
        symmetry: None,
        allow_deadlock: None,
        check_liveness: None,
        count_satisfying: vec![],
        continue_on_violation: false,
        state_constraint: None,
        config_path: None,
    };
    let out = runner::check_spec(&input);
    let _ = std::fs::remove_file(&spec_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_dir(&dir);

    match out.outcome {
        CheckOutcome::Ok { stats } => {
            assert_eq!(
                stats.states_explored, 10,
                "CLI Cap=10 should win over cfg Cap=5; got {} states (cfg-bound would be 5)",
                stats.states_explored
            );
        }
        other => panic!("expected ok with CLI-overridden bound, got {:?}", other),
    }
}

const DEMO_MANIFEST: &str = "test_cases/demo/Counter.demo.json";

fn unique_temp_dir(tag: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("tla_demo_{}_{}", tag, std::process::id()));
    let _ = std::fs::remove_dir_all(&p);
    std::fs::create_dir_all(&p).expect("create temp dir");
    p
}

#[test]
fn validate_demo_passes_and_includes_traces() {
    let out = runner::validate_demo(&ValidateDemoInput {
        manifest_path: DEMO_MANIFEST.to_string(),
    });
    assert!(
        matches!(out.status, DemoStatus::Passed),
        "expected Passed, got {:?} ({:?})",
        out.status,
        out.error
    );
    assert_eq!(out.beats.len(), 2);
    assert_eq!(out.title.as_deref(), Some("Counter overflow demo"));

    let compare_beat = out
        .beats
        .iter()
        .find(|b| b.runs.len() == 2)
        .expect("a compare beat with two variant runs");
    assert!(compare_beat.passed);
    assert!(out.beats[0].runs[0].trace.len() >= 2);
    assert!(out.beats[0].runs[0].assertions.iter().all(|a| a.passed));
}

#[test]
fn validate_demo_reports_error_for_missing_manifest() {
    let out = runner::validate_demo(&ValidateDemoInput {
        manifest_path: "does_not_exist.demo.json".to_string(),
    });
    assert!(matches!(out.status, DemoStatus::Error));
    assert!(out.error.is_some());
}

#[test]
fn append_beat_validate_only_does_not_write() {
    let out = runner::append_beat(&AppendBeatInput {
        manifest_path: DEMO_MANIFEST.to_string(),
        title: "preview only".to_string(),
        variant: Some("low".to_string()),
        compare: Vec::new(),
        scenario: vec!["action: Inc".to_string()],
        note: None,
        expect: vec!["final: x = 1".to_string()],
        expect_per_variant: BTreeMap::new(),
        validate_only: true,
    });
    assert!(!out.written);
    assert!(matches!(out.status, DemoStatus::Passed));
}

#[test]
fn append_beat_writes_and_reloads() {
    let dir = unique_temp_dir("append");
    std::fs::copy("test_cases/demo/Counter.tla", dir.join("Counter.tla")).unwrap();
    std::fs::copy(DEMO_MANIFEST, dir.join("Counter.demo.json")).unwrap();
    let manifest_path = dir.join("Counter.demo.json").to_string_lossy().to_string();

    let out = runner::append_beat(&AppendBeatInput {
        manifest_path: manifest_path.clone(),
        title: "Reset returns to zero".to_string(),
        variant: Some("low".to_string()),
        compare: Vec::new(),
        scenario: vec!["action: Inc".to_string(), "action: Reset".to_string()],
        note: Some("reset clears the counter".to_string()),
        expect: vec!["final: x = 0".to_string()],
        expect_per_variant: BTreeMap::new(),
        validate_only: false,
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);
    assert!(out.written);

    let reloaded = runner::validate_demo(&ValidateDemoInput {
        manifest_path: manifest_path.clone(),
    });
    assert_eq!(reloaded.beats.len(), 3);
    assert!(matches!(reloaded.status, DemoStatus::Passed));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn append_beat_rejects_unknown_variant() {
    let dir = unique_temp_dir("badvariant");
    std::fs::copy("test_cases/demo/Counter.tla", dir.join("Counter.tla")).unwrap();
    std::fs::copy(DEMO_MANIFEST, dir.join("Counter.demo.json")).unwrap();
    let manifest_path = dir.join("Counter.demo.json").to_string_lossy().to_string();

    let out = runner::append_beat(&AppendBeatInput {
        manifest_path: manifest_path.clone(),
        title: "bad".to_string(),
        variant: Some("nope".to_string()),
        compare: Vec::new(),
        scenario: vec!["action: Inc".to_string()],
        note: None,
        expect: Vec::new(),
        expect_per_variant: BTreeMap::new(),
        validate_only: false,
    });
    assert!(matches!(out.status, DemoStatus::Error));
    assert!(!out.written);

    let reloaded = runner::validate_demo(&ValidateDemoInput { manifest_path });
    assert_eq!(reloaded.beats.len(), 2, "broken beat must not be persisted");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn append_beat_does_not_write_when_assertion_fails() {
    let dir = unique_temp_dir("failassert");
    std::fs::copy("test_cases/demo/Counter.tla", dir.join("Counter.tla")).unwrap();
    std::fs::copy(DEMO_MANIFEST, dir.join("Counter.demo.json")).unwrap();
    let manifest_path = dir.join("Counter.demo.json").to_string_lossy().to_string();

    let out = runner::append_beat(&AppendBeatInput {
        manifest_path: manifest_path.clone(),
        title: "runs but expectation is wrong".to_string(),
        variant: Some("low".to_string()),
        compare: Vec::new(),
        scenario: vec!["action: Inc".to_string()],
        note: None,
        expect: vec!["final: x = 99".to_string()],
        expect_per_variant: BTreeMap::new(),
        validate_only: false,
    });
    assert!(matches!(out.status, DemoStatus::Failed));
    assert!(
        !out.written,
        "a beat with a failing assertion must not be persisted"
    );
    let beat = out.beat.expect("summary returned for diagnosis");
    assert!(beat.runs[0].assertions.iter().any(|a| !a.passed));

    let reloaded = runner::validate_demo(&ValidateDemoInput { manifest_path });
    assert_eq!(
        reloaded.beats.len(),
        2,
        "failing beat must not be persisted"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn export_demo_doc_writes_markdown() {
    let dir = unique_temp_dir("doc");
    let out_path = dir.join("walkthrough.md").to_string_lossy().to_string();

    let out = runner::export_demo_doc(&ExportDemoDocInput {
        manifest_path: DEMO_MANIFEST.to_string(),
        out_path: out_path.clone(),
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);
    assert_eq!(out.written_path.as_deref(), Some(out_path.as_str()));

    let contents = std::fs::read_to_string(&out_path).unwrap();
    assert!(contents.contains("Counter overflow demo"));
    assert!(contents.contains("action: Inc"));
    assert!(contents.contains('✓'));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn validate_demo_loads_toml_manifest() {
    let dir = unique_temp_dir("toml_load");
    std::fs::copy("test_cases/demo/Counter.tla", dir.join("Counter.tla")).unwrap();
    let manifest_path = dir.join("Counter.demo.toml");
    std::fs::write(
        &manifest_path,
        r#"
title = "toml demo"
[variants.low]
spec = "Counter.tla"
constants = { Max = "2" }
[[beats]]
title = "one increment"
variant = "low"
scenario = ["action: Inc"]
expect = ["final: x = 1", "all: x <= Max"]
"#,
    )
    .unwrap();

    let out = runner::validate_demo(&ValidateDemoInput {
        manifest_path: manifest_path.to_string_lossy().to_string(),
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);
    assert_eq!(out.beats.len(), 1);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn append_beat_preserves_toml_format() {
    let dir = unique_temp_dir("toml_append");
    std::fs::copy("test_cases/demo/Counter.tla", dir.join("Counter.tla")).unwrap();
    let manifest_path = dir.join("Counter.demo.toml");
    std::fs::write(
        &manifest_path,
        r#"
title = "toml demo"
[variants.low]
spec = "Counter.tla"
constants = { Max = "2" }
[[beats]]
title = "one increment"
variant = "low"
scenario = ["action: Inc"]
expect = ["final: x = 1"]
"#,
    )
    .unwrap();
    let mp = manifest_path.to_string_lossy().to_string();

    let out = runner::append_beat(&AppendBeatInput {
        manifest_path: mp.clone(),
        title: "reset to zero".to_string(),
        variant: Some("low".to_string()),
        compare: Vec::new(),
        scenario: vec!["action: Inc".to_string(), "action: Reset".to_string()],
        note: None,
        expect: vec!["final: x = 0".to_string()],
        expect_per_variant: BTreeMap::new(),
        validate_only: false,
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);
    assert!(out.written);

    let written = std::fs::read_to_string(&manifest_path).unwrap();
    assert!(
        written.contains("[[beats]]"),
        "file must stay TOML, got:\n{}",
        written
    );
    assert!(
        !written.trim_start().starts_with('{'),
        "file must not become JSON"
    );

    let reloaded = runner::validate_demo(&ValidateDemoInput { manifest_path: mp });
    assert_eq!(reloaded.beats.len(), 2);
    assert!(matches!(reloaded.status, DemoStatus::Passed));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn export_demo_html_writes_self_contained_file() {
    let dir = unique_temp_dir("html_export");
    let out_path = dir.join("walk.html").to_string_lossy().to_string();

    let out = runner::export_demo_html(&ExportDemoHtmlInput {
        manifest_path: "test_cases/demo/Counter.demo.json".to_string(),
        out_path: out_path.clone(),
        explorable: false,
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);
    assert_eq!(out.written_path.as_deref(), Some(out_path.as_str()));

    let contents = std::fs::read_to_string(&out_path).unwrap();
    assert!(contents.contains("Counter overflow demo"));
    assert!(contents.contains("const DATA ="));
    assert!(!contents.contains("https://"), "must stay self-contained");

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(feature = "embed-wasm")]
#[test]
fn export_demo_html_explorable_embeds_engine() {
    let dir = unique_temp_dir("html_explorable");
    let out_path = dir.join("explorer.html").to_string_lossy().to_string();

    let out = runner::export_demo_html(&ExportDemoHtmlInput {
        manifest_path: "test_cases/demo/Counter.demo.json".to_string(),
        out_path: out_path.clone(),
        explorable: true,
    });
    assert!(matches!(out.status, DemoStatus::Passed), "{:?}", out.error);

    let contents = std::fs::read_to_string(&out_path).unwrap();
    assert!(
        contents.contains("export function explore_init"),
        "engine bindings must be inlined"
    );
    assert!(
        !contents.contains("const WASM_B64 = \"\""),
        "embedded wasm must be non-empty"
    );
    assert!(!contents.contains("https://"), "must stay self-contained");

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(not(feature = "embed-wasm"))]
#[test]
fn export_demo_html_explorable_requires_embed_wasm() {
    let dir = unique_temp_dir("html_explorable_noembed");
    let out_path = dir.join("explorer.html").to_string_lossy().to_string();

    let out = runner::export_demo_html(&ExportDemoHtmlInput {
        manifest_path: "test_cases/demo/Counter.demo.json".to_string(),
        out_path,
        explorable: true,
    });
    assert!(matches!(out.status, DemoStatus::Error));
    let msg = format!("{:?}", out.error);
    assert!(
        msg.contains("embed-wasm"),
        "error should name the feature: {msg}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
