use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::Source;
use crate::ast::{Env, Spec};
use crate::checker::{
    CheckResult, CheckStats, CheckerConfig, Counterexample, PrepareSpecError, PropertyStats, check,
};
use crate::config::{apply_config, parse_cfg, parse_constant_value};
use crate::demo::{self, Beat, BeatReport, Manifest, run_beat};
use crate::liveness::LivenessViolation;
use crate::parser::{parse_expr, parse_with_warnings};
use crate::scenario::{ScenarioResult, execute_scenario, parse_scenario};

use super::SCHEMA_VERSION;
use super::schema::{
    ActionSummary, AppendBeatInput, AppendBeatOutput, AssertionSummary, BeatSummary, CheckOutcome,
    CheckSpecInput, CheckSpecOutput, CheckStatsSummary, ConstantBinding, DemoStatus,
    DemoTraceState, ErrorPhase, ExportDemoDocInput, ExportDemoDocOutput, InvariantSummary,
    LimitKind, ListInvariantsInput, ListInvariantsOutput, ParseWarning, PropertySummary,
    ReplayScenarioInput, ReplayScenarioOutput, ScenarioFailureInfo, ScenarioTraceState, SourceSpan,
    SpecSummary, StateSnapshot, StructuredError, TlaValue, ValidateDemoInput, ValidateDemoOutput,
    ValidateSpecInput, ValidateSpecOutput, VariantRunSummary,
};

pub struct LoadedSpec {
    pub spec: Spec,
    pub source: Source,
    pub domains: Env,
    pub spec_path: PathBuf,
    pub checker_config: CheckerConfig,
    pub warnings: Vec<ParseWarning>,
}

pub fn prepare(
    spec_path: &str,
    config_path: Option<&str>,
    user_constants: &BTreeMap<String, String>,
) -> Result<LoadedSpec, StructuredError> {
    let path = PathBuf::from(spec_path);
    let contents = fs::read_to_string(&path)
        .map_err(|e| StructuredError::io(format!("failed to read {}: {}", spec_path, e)))?;
    let source = Source::new(spec_path.to_string(), contents.clone());

    let (mut spec, parser_warnings) = parse_with_warnings(&contents).map_err(|err| {
        let span = err
            .span
            .and_then(|s| (!s.is_empty()).then(|| SourceSpan::from_span(s, &source)));
        StructuredError::parse(err.message.clone(), span)
    })?;
    let warnings: Vec<ParseWarning> = parser_warnings
        .iter()
        .map(|w| ParseWarning::from_spanned(w, &source))
        .collect();

    let mut domains = Env::new();
    let mut checker_config = CheckerConfig {
        spec_path: Some(path.clone()),
        quiet: true,
        ..CheckerConfig::default()
    };

    let cli_constants: Vec<(Arc<str>, crate::ast::Value)> = user_constants
        .iter()
        .map(|(name, value_str)| {
            let value = parse_constant_value(value_str).ok_or_else(|| {
                StructuredError::constant(format!(
                    "could not parse constant {}={:?}",
                    name, value_str
                ))
            })?;
            Ok::<_, StructuredError>((Arc::from(name.as_str()), value))
        })
        .collect::<Result<_, _>>()?;

    let auto_cfg = Path::new(&path).with_extension("cfg");
    let cfg_path: Option<PathBuf> = match config_path {
        Some(p) => Some(PathBuf::from(p)),
        None if auto_cfg.exists() => Some(auto_cfg),
        _ => None,
    };

    if let Some(cfg) = cfg_path {
        let cfg_contents = fs::read_to_string(&cfg).map_err(|e| {
            StructuredError::config(format!("failed to read cfg {}: {}", cfg.display(), e))
        })?;
        let cfg_parsed = parse_cfg(&cfg_contents)
            .map_err(|e| StructuredError::config(format!("cfg parse error: {}", e)))?;
        apply_config(
            &cfg_parsed,
            &mut spec,
            &mut domains,
            &mut checker_config,
            &cli_constants,
            &[],
            false,
        )
        .map_err(|e| StructuredError::config(format!("cfg apply error: {}", e)))?;
    }

    for (name, value) in cli_constants {
        domains.insert(name, value);
    }

    Ok(LoadedSpec {
        spec,
        source,
        domains,
        spec_path: path,
        checker_config,
        warnings,
    })
}

pub fn validate_spec(input: &ValidateSpecInput) -> ValidateSpecOutput {
    match prepare(
        &input.spec_path,
        input.config_path.as_deref(),
        &input.constants,
    ) {
        Ok(loaded) => ValidateSpecOutput::ok(
            summarize_spec(&loaded.spec, &loaded.domains),
            loaded.warnings,
        ),
        Err(err) => ValidateSpecOutput::error(err),
    }
}

pub fn list_invariants(input: &ListInvariantsInput) -> ListInvariantsOutput {
    match prepare(
        &input.spec_path,
        input.config_path.as_deref(),
        &input.constants,
    ) {
        Ok(loaded) => ListInvariantsOutput::ok(invariant_summaries(&loaded.spec), loaded.warnings),
        Err(err) => ListInvariantsOutput::error(err),
    }
}

pub fn replay_scenario(input: &ReplayScenarioInput) -> ReplayScenarioOutput {
    let loaded = match prepare(
        &input.spec_path,
        input.config_path.as_deref(),
        &input.constants,
    ) {
        Ok(loaded) => loaded,
        Err(err) => return ReplayScenarioOutput::error(err),
    };

    let scenario = match parse_scenario(&input.scenario) {
        Ok(s) => s,
        Err(msg) => return ReplayScenarioOutput::error(StructuredError::parse(msg, None)),
    };

    match execute_scenario(&loaded.spec, &scenario, &loaded.domains) {
        Ok(result) => scenario_result_to_output(result, &loaded.spec),
        Err(err) => {
            ReplayScenarioOutput::error(StructuredError::from_eval(&err, Some(&loaded.source)))
        }
    }
}

fn scenario_result_to_output(result: ScenarioResult, spec: &Spec) -> ReplayScenarioOutput {
    let trace: Vec<ScenarioTraceState> = result
        .states
        .iter()
        .enumerate()
        .map(|(idx, (_step, state, changes))| ScenarioTraceState {
            step_index: if idx == 0 { None } else { Some(idx - 1) },
            state: StateSnapshot::from_state(state, &spec.vars),
            changes: changes.clone(),
        })
        .collect();

    match result.failure {
        Some(failure) => ReplayScenarioOutput::failed(
            trace,
            ScenarioFailureInfo {
                step_index: failure.step_index,
                message: failure.message,
                available_actions: failure.available_actions,
            },
        ),
        None => ReplayScenarioOutput::ok(trace),
    }
}

pub fn check_spec(input: &CheckSpecInput) -> CheckSpecOutput {
    let mut loaded = match prepare(
        &input.spec_path,
        input.config_path.as_deref(),
        &input.constants,
    ) {
        Ok(loaded) => loaded,
        Err(err) => {
            return CheckSpecOutput::new(CheckOutcome::Error {
                phase: error_phase_for(&err.kind),
                error: err,
                partial_stats: None,
            });
        }
    };

    loaded.checker_config.max_states = input.max_states as usize;
    loaded.checker_config.max_depth = input.max_depth as usize;
    loaded.checker_config.max_seconds = Some(input.max_seconds);
    if let Some(allow_deadlock) = input.allow_deadlock {
        loaded.checker_config.allow_deadlock = allow_deadlock;
    }
    if let Some(check_liveness) = input.check_liveness {
        loaded.checker_config.check_liveness = check_liveness;
    }
    loaded.checker_config.continue_on_violation = input.continue_on_violation;
    loaded.checker_config.count_properties = input
        .count_satisfying
        .iter()
        .map(|n| Arc::from(n.as_str()))
        .collect();
    if let Some(sym) = &input.symmetry {
        let sym_arc: Arc<str> = Arc::from(sym.as_str());
        if !loaded
            .checker_config
            .symmetric_constants
            .iter()
            .any(|s| s == &sym_arc)
        {
            loaded.checker_config.symmetric_constants.push(sym_arc);
        }
    }

    if let Some(constraint_src) = &input.state_constraint {
        match parse_expr(constraint_src) {
            Ok(expr) => loaded.checker_config.state_constraints.push(expr),
            Err(err) => {
                let constraint_source =
                    Source::new("<state_constraint>".to_string(), constraint_src.clone());
                let span = err.span.and_then(|s| {
                    (!s.is_empty()).then(|| SourceSpan::from_span(s, &constraint_source))
                });
                return CheckSpecOutput::new(CheckOutcome::Error {
                    phase: ErrorPhase::Config,
                    error: StructuredError::parse(
                        format!("state_constraint parse error: {}", err.message),
                        span,
                    ),
                    partial_stats: None,
                });
            }
        }
    }

    let advisories = collect_advisories(input);

    let result = check(&loaded.spec, &loaded.domains, &loaded.checker_config);
    CheckSpecOutput::new(map_check_result(result, &loaded.spec, &loaded.source))
        .with_advisories(advisories)
}

fn collect_advisories(input: &CheckSpecInput) -> Vec<String> {
    let mut advisories = Vec::new();
    if input.max_depth > 100 {
        advisories.push(format!(
            "max_depth={} is high; most algorithmic bugs surface at depth < 50. \
             Consider shrinking unless you have evidence a deeper trace is needed.",
            input.max_depth
        ));
    }
    if input.max_states > 1_000_000 {
        advisories.push(format!(
            "max_states={} is large. Start with smaller constants and grow the budget on evidence \
             (states/sec from a small run × target wall-clock).",
            input.max_states
        ));
    }
    advisories
}

fn error_phase_for(kind: &super::schema::ErrorKind) -> ErrorPhase {
    use super::schema::ErrorKind;
    match kind {
        ErrorKind::Io => ErrorPhase::Io,
        ErrorKind::Parse => ErrorPhase::Parse,
        ErrorKind::Config => ErrorPhase::Config,
        ErrorKind::Constant => ErrorPhase::Constant,
        ErrorKind::Eval => ErrorPhase::Internal,
        ErrorKind::Internal => ErrorPhase::Internal,
    }
}

fn map_check_result(result: CheckResult, spec: &Spec, source: &Source) -> CheckOutcome {
    match result {
        CheckResult::Ok(stats) => CheckOutcome::Ok {
            stats: summarize_stats(&stats),
        },
        CheckResult::InvariantViolation(cex, stats) => {
            let invariant = invariant_name(spec, cex.violated_invariant);
            let (trace, actions) = counterexample_to_snapshots(&cex, spec);
            CheckOutcome::InvariantViolation {
                invariant,
                trace,
                actions,
                stats: summarize_stats(&stats),
            }
        }
        CheckResult::Deadlock(trace, actions, stats) => CheckOutcome::Deadlock {
            trace: trace
                .iter()
                .map(|s| StateSnapshot::from_state(s, &spec.vars))
                .collect(),
            actions: actions
                .into_iter()
                .map(|a| a.map(|s| s.to_string()))
                .collect(),
            stats: summarize_stats(&stats),
        },
        CheckResult::LivenessViolation(violation, stats) => {
            map_liveness_violation(violation, spec, stats)
        }
        CheckResult::MaxStatesExceeded(stats) => CheckOutcome::LimitReached {
            limit: LimitKind::MaxStates,
            stats: summarize_stats(&stats),
        },
        CheckResult::MaxDepthExceeded(stats) => CheckOutcome::LimitReached {
            limit: LimitKind::MaxDepth,
            stats: summarize_stats(&stats),
        },
        CheckResult::MaxTimeExceeded(stats) => CheckOutcome::LimitReached {
            limit: LimitKind::MaxSeconds,
            stats: summarize_stats(&stats),
        },
        CheckResult::InitError(err) => CheckOutcome::Error {
            phase: ErrorPhase::Init,
            error: StructuredError::from_eval(&err, Some(source)),
            partial_stats: None,
        },
        CheckResult::NextError(err, _trace, _dot) => CheckOutcome::Error {
            phase: ErrorPhase::Next,
            error: StructuredError::from_eval(&err, Some(source)),
            partial_stats: None,
        },
        CheckResult::InvariantError(err, _trace, _dot) => CheckOutcome::Error {
            phase: ErrorPhase::Invariant,
            error: StructuredError::from_eval(&err, Some(source)),
            partial_stats: None,
        },
        CheckResult::NoInitialStates => CheckOutcome::Error {
            phase: ErrorPhase::Init,
            error: StructuredError::internal("no initial states found"),
            partial_stats: None,
        },
        CheckResult::PrepareError(err) => map_prepare_error(err, source),
    }
}

fn map_liveness_violation(
    violation: LivenessViolation,
    spec: &Spec,
    stats: CheckStats,
) -> CheckOutcome {
    CheckOutcome::LivenessViolation {
        property: violation.property,
        prefix: violation
            .prefix
            .iter()
            .map(|s| StateSnapshot::from_state(s, &spec.vars))
            .collect(),
        cycle: violation
            .cycle
            .iter()
            .map(|s| StateSnapshot::from_state(s, &spec.vars))
            .collect(),
        stats: summarize_stats(&stats),
    }
}

fn map_prepare_error(err: PrepareSpecError, source: &Source) -> CheckOutcome {
    let outcome = match err {
        PrepareSpecError::InstanceError(eval_err) => (
            ErrorPhase::Config,
            StructuredError::from_eval(&eval_err, Some(source)),
        ),
        PrepareSpecError::MissingConstants(names) => (
            ErrorPhase::Constant,
            StructuredError::constant(format!(
                "missing constants: {}",
                names
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        ),
        PrepareSpecError::AssumeViolation(idx) => (
            ErrorPhase::Init,
            StructuredError::internal(format!("ASSUME #{} evaluated to FALSE", idx)),
        ),
        PrepareSpecError::AssumeError(idx, eval_err) => {
            let mut err = StructuredError::from_eval(&eval_err, Some(source));
            err.message = format!("ASSUME #{}: {}", idx, err.message);
            (ErrorPhase::Init, err)
        }
    };
    CheckOutcome::Error {
        phase: outcome.0,
        error: outcome.1,
        partial_stats: None,
    }
}

fn invariant_name(spec: &Spec, idx: usize) -> Option<String> {
    spec.invariant_names
        .get(idx)
        .and_then(|n| n.as_ref().map(|s| s.to_string()))
}

fn counterexample_to_snapshots(
    cex: &Counterexample,
    spec: &Spec,
) -> (Vec<StateSnapshot>, Vec<Option<String>>) {
    let trace = cex
        .trace
        .iter()
        .map(|s| StateSnapshot::from_state(s, &spec.vars))
        .collect();
    let actions = cex
        .actions
        .iter()
        .map(|a| a.as_ref().map(|s| s.to_string()))
        .collect();
    (trace, actions)
}

fn summarize_stats(stats: &CheckStats) -> CheckStatsSummary {
    let mut actions: Vec<ActionSummary> = stats
        .transitions_by_action
        .iter()
        .map(|(name, count)| ActionSummary {
            name: name.as_ref().map(|n| n.to_string()),
            transitions: *count as u64,
        })
        .collect();
    actions.sort_by_key(|a| std::cmp::Reverse(a.transitions));

    CheckStatsSummary {
        states_explored: stats.states_explored as u64,
        transitions: stats.transitions as u64,
        max_depth_reached: stats.max_depth_reached as u64,
        elapsed_secs: stats.elapsed_secs,
        actions,
        property_stats: stats
            .property_stats
            .iter()
            .map(summarize_property)
            .collect(),
        violation_count: if stats.violation_count == 0 {
            None
        } else {
            Some(stats.violation_count as u64)
        },
    }
}

fn summarize_property(p: &PropertyStats) -> PropertySummary {
    PropertySummary {
        name: p.name.to_string(),
        satisfied: p.satisfied as u64,
        violated: p.violated as u64,
        errors: p.errors as u64,
    }
}

fn summarize_spec(spec: &Spec, domains: &Env) -> SpecSummary {
    let constants = spec
        .constants
        .iter()
        .map(|name| ConstantBinding {
            name: name.to_string(),
            value: domains.get(name).map(TlaValue::from_value),
        })
        .collect();
    SpecSummary {
        vars: spec.vars.iter().map(|v| v.to_string()).collect(),
        constants,
        invariants: invariant_summaries(spec),
        has_init: spec.init.is_some(),
        has_next: spec.next.is_some(),
        definition_count: spec.definitions.len(),
    }
}

fn invariant_summaries(spec: &Spec) -> Vec<InvariantSummary> {
    spec.invariant_names
        .iter()
        .map(|name| InvariantSummary {
            name: name.as_ref().map(|n| n.to_string()),
        })
        .collect()
}

fn manifest_dir(manifest_path: &str) -> PathBuf {
    Path::new(manifest_path)
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."))
}

fn variant_run_to_summary(run: &demo::VariantRun) -> VariantRunSummary {
    VariantRunSummary {
        variant: run.variant.clone(),
        passed: run.passed(),
        failure: run.failure.clone(),
        assertions: run
            .assertions
            .iter()
            .map(|a| AssertionSummary {
                expectation: a.raw.clone(),
                passed: a.passed,
                detail: a.detail.clone(),
            })
            .collect(),
        trace: run
            .trace
            .iter()
            .map(|t| DemoTraceState {
                label: t.label.clone(),
                changes: t.changes.clone(),
                state: StateSnapshot::from_state(&t.state, &run.vars),
            })
            .collect(),
    }
}

fn beat_report_to_summary(index: usize, report: &BeatReport) -> BeatSummary {
    BeatSummary {
        index,
        title: report.title.clone(),
        note: report.note.clone(),
        passed: report.passed(),
        runs: report.runs.iter().map(variant_run_to_summary).collect(),
    }
}

pub fn validate_demo(input: &ValidateDemoInput) -> ValidateDemoOutput {
    let manifest = match Manifest::load(Path::new(&input.manifest_path)) {
        Ok(m) => m,
        Err(e) => {
            return ValidateDemoOutput {
                schema_version: SCHEMA_VERSION.to_string(),
                status: DemoStatus::Error,
                title: None,
                beats: Vec::new(),
                error: Some(StructuredError::config(e)),
            };
        }
    };

    let dir = manifest_dir(&input.manifest_path);
    let mut beats = Vec::new();
    let mut all_passed = true;
    let mut any_error = false;
    for (idx, beat) in manifest.beats.iter().enumerate() {
        let report = run_beat(&dir, &manifest, beat);
        all_passed &= report.passed();
        if report.runs.iter().any(|r| r.failure.is_some()) {
            any_error = true;
        }
        beats.push(beat_report_to_summary(idx, &report));
    }

    let status = if any_error {
        DemoStatus::Error
    } else if all_passed {
        DemoStatus::Passed
    } else {
        DemoStatus::Failed
    };

    ValidateDemoOutput {
        schema_version: SCHEMA_VERSION.to_string(),
        status,
        title: manifest.title.clone(),
        beats,
        error: None,
    }
}

pub fn append_beat(input: &AppendBeatInput) -> AppendBeatOutput {
    let manifest_path = Path::new(&input.manifest_path);
    let mut manifest = match Manifest::load(manifest_path) {
        Ok(m) => m,
        Err(e) => {
            return AppendBeatOutput {
                schema_version: SCHEMA_VERSION.to_string(),
                status: DemoStatus::Error,
                written: false,
                beat: None,
                error: Some(StructuredError::config(e)),
            };
        }
    };

    let beat = Beat {
        title: input.title.clone(),
        variant: input.variant.clone(),
        compare: input.compare.clone(),
        scenario: input.scenario.clone(),
        replay: None,
        note: input.note.clone(),
        expect: input.expect.clone(),
        expect_per_variant: input.expect_per_variant.clone(),
    };

    manifest.beats.push(beat.clone());
    if let Err(e) = manifest.validate() {
        return AppendBeatOutput {
            schema_version: SCHEMA_VERSION.to_string(),
            status: DemoStatus::Error,
            written: false,
            beat: None,
            error: Some(StructuredError::config(e)),
        };
    }

    let dir = manifest_dir(&input.manifest_path);
    let report = run_beat(&dir, &manifest, &beat);
    let runnable = report.runs.iter().all(|r| r.failure.is_none());
    let summary = beat_report_to_summary(manifest.beats.len() - 1, &report);

    let mut written = false;
    if !input.validate_only && runnable {
        let serialized = match manifest.serialize_for(manifest_path) {
            Ok(s) => s,
            Err(e) => {
                return AppendBeatOutput {
                    schema_version: SCHEMA_VERSION.to_string(),
                    status: DemoStatus::Error,
                    written: false,
                    beat: Some(summary),
                    error: Some(StructuredError::config(e)),
                };
            }
        };
        if let Err(e) = fs::write(manifest_path, serialized) {
            return AppendBeatOutput {
                schema_version: SCHEMA_VERSION.to_string(),
                status: DemoStatus::Error,
                written: false,
                beat: Some(summary),
                error: Some(StructuredError::io(format!(
                    "failed to write manifest {}: {}",
                    input.manifest_path, e
                ))),
            };
        }
        written = true;
    }

    let status = if !runnable {
        DemoStatus::Error
    } else if report.passed() {
        DemoStatus::Passed
    } else {
        DemoStatus::Failed
    };

    AppendBeatOutput {
        schema_version: SCHEMA_VERSION.to_string(),
        status,
        written,
        beat: Some(summary),
        error: None,
    }
}

pub fn export_demo_doc(input: &ExportDemoDocInput) -> ExportDemoDocOutput {
    let manifest = match Manifest::load(Path::new(&input.manifest_path)) {
        Ok(m) => m,
        Err(e) => {
            return ExportDemoDocOutput {
                schema_version: SCHEMA_VERSION.to_string(),
                status: DemoStatus::Error,
                written_path: None,
                error: Some(StructuredError::config(e)),
            };
        }
    };

    let dir = manifest_dir(&input.manifest_path);
    let (markdown, all_passed) = demo::render_doc(&dir, &manifest);

    match fs::write(&input.out_path, markdown) {
        Ok(()) => ExportDemoDocOutput {
            schema_version: SCHEMA_VERSION.to_string(),
            status: if all_passed {
                DemoStatus::Passed
            } else {
                DemoStatus::Failed
            },
            written_path: Some(input.out_path.clone()),
            error: None,
        },
        Err(e) => ExportDemoDocOutput {
            schema_version: SCHEMA_VERSION.to_string(),
            status: DemoStatus::Error,
            written_path: None,
            error: Some(StructuredError::io(format!(
                "failed to write doc {}: {}",
                input.out_path, e
            ))),
        },
    }
}
