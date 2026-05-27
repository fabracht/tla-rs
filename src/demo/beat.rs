use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::{Env, Expr, State, Value};
use crate::checker::prepare_spec;
use crate::config::parse_constant_value;
use crate::eval::Definitions;
use crate::load::prepare_from_path;
use crate::parser::parse_expr;
use crate::scenario::{ScenarioStep, compute_changes, execute_scenario_with, parse_scenario};
use crate::trace_io::json_to_state;

use super::manifest::{Beat, Manifest, Variant};

pub struct TraceStep {
    pub label: String,
    pub changes: Vec<String>,
    pub state: State,
}

pub struct AssertionResult {
    pub raw: String,
    pub passed: bool,
    pub detail: Option<String>,
}

pub struct VariantRun {
    pub variant: String,
    pub vars: Vec<Arc<str>>,
    pub trace: Vec<TraceStep>,
    pub failure: Option<String>,
    pub assertions: Vec<AssertionResult>,
}

impl VariantRun {
    pub fn passed(&self) -> bool {
        self.failure.is_none() && self.assertions.iter().all(|a| a.passed)
    }
}

pub struct BeatReport {
    pub title: String,
    pub note: Option<String>,
    pub runs: Vec<VariantRun>,
}

impl BeatReport {
    pub fn passed(&self) -> bool {
        !self.runs.is_empty() && self.runs.iter().all(VariantRun::passed)
    }
}

pub fn run_beat(manifest_dir: &Path, manifest: &Manifest, beat: &Beat) -> BeatReport {
    let runs = beat
        .target_variants()
        .iter()
        .map(|name| match manifest.variants.get(name) {
            Some(variant) => run_variant(manifest_dir, beat, name, variant),
            None => VariantRun {
                variant: name.clone(),
                vars: Vec::new(),
                trace: Vec::new(),
                failure: Some(format!("unknown variant {:?}", name)),
                assertions: Vec::new(),
            },
        })
        .collect();

    BeatReport {
        title: beat.title.clone(),
        note: beat.note.clone(),
        runs,
    }
}

fn run_variant(manifest_dir: &Path, beat: &Beat, name: &str, variant: &Variant) -> VariantRun {
    let fail = |msg: String| VariantRun {
        variant: name.to_string(),
        vars: Vec::new(),
        trace: Vec::new(),
        failure: Some(msg),
        assertions: Vec::new(),
    };

    let constants = match parse_variant_constants(variant) {
        Ok(c) => c,
        Err(e) => return fail(e),
    };

    let spec_path = manifest_dir.join(&variant.spec);
    let config_path: Option<PathBuf> = variant.config.as_ref().map(|c| manifest_dir.join(c));

    let prepared = match prepare_from_path(&spec_path, config_path.as_deref(), &constants) {
        Ok(p) => p,
        Err(e) => return fail(format!("{}", e)),
    };

    let (env, defs) = match prepare_spec(
        &prepared.spec,
        &prepared.domains,
        Some(&prepared.spec_path),
        true,
    ) {
        Ok(pair) => pair,
        Err(e) => return fail(format!("prepare spec failed: {:?}", e)),
    };

    let vars = prepared.spec.vars.clone();

    let (trace, failure) = if !beat.scenario.is_empty() {
        run_scenario(beat, &prepared.spec, &env, &defs)
    } else if let Some(replay) = &beat.replay {
        match load_replay(&manifest_dir.join(replay), &vars) {
            Ok(t) => (t, None),
            Err(e) => return fail(e),
        }
    } else {
        return fail("beat has neither scenario nor replay".to_string());
    };

    let states: Vec<&State> = trace.iter().map(|s| &s.state).collect();
    let assertions = run_assertions(beat.expectations_for(name), &states, &vars, &env, &defs);

    VariantRun {
        variant: name.to_string(),
        vars,
        trace,
        failure,
        assertions,
    }
}

fn run_scenario(
    beat: &Beat,
    spec: &crate::ast::Spec,
    env: &Env,
    defs: &Definitions,
) -> (Vec<TraceStep>, Option<String>) {
    let scenario = match parse_scenario(&beat.scenario.join("\n")) {
        Ok(s) => s,
        Err(e) => return (Vec::new(), Some(format!("scenario parse error: {}", e))),
    };

    match execute_scenario_with(spec, &scenario, env, defs) {
        Ok(result) => {
            let trace = result
                .states
                .iter()
                .enumerate()
                .map(|(idx, (step, state, changes))| TraceStep {
                    label: step_label(idx, step),
                    changes: changes.clone(),
                    state: state.clone(),
                })
                .collect();
            let failure = result.failure.map(|f| {
                format!(
                    "scenario failed at step {}: {}",
                    f.step_index + 1,
                    f.message
                )
            });
            (trace, failure)
        }
        Err(e) => (Vec::new(), Some(format!("scenario eval error: {:?}", e))),
    }
}

fn step_label(idx: usize, step: &ScenarioStep) -> String {
    if idx == 0 {
        return "Init".to_string();
    }
    match step {
        ScenarioStep::Action { name, .. } => name.to_string(),
        ScenarioStep::Condition(_) => format!("step {}", idx),
    }
}

fn parse_variant_constants(variant: &Variant) -> Result<Vec<(Arc<str>, Value)>, String> {
    variant
        .constants
        .iter()
        .map(|(name, raw)| {
            let value = parse_constant_value(raw)
                .ok_or_else(|| format!("could not parse constant {}={:?}", name, raw))?;
            Ok((Arc::from(name.as_str()), value))
        })
        .collect()
}

fn load_replay(path: &Path, vars: &[Arc<str>]) -> Result<Vec<TraceStep>, String> {
    let contents = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read replay {}: {}", path.display(), e))?;
    let json: serde_json::Value =
        serde_json::from_str(&contents).map_err(|e| format!("replay parse error: {}", e))?;
    let arr = json
        .get("trace")
        .and_then(|t| t.as_array())
        .ok_or_else(|| "replay file missing 'trace' array".to_string())?;

    let mut steps: Vec<TraceStep> = Vec::new();
    for (idx, entry) in arr.iter().enumerate() {
        let state_json = entry
            .get("state")
            .ok_or_else(|| format!("replay trace[{}] missing 'state'", idx))?;
        let state = json_to_state(state_json, vars)
            .ok_or_else(|| format!("replay trace[{}] state could not be parsed", idx))?;
        let action = entry
            .get("action")
            .and_then(|a| a.as_str())
            .map(|s| s.to_string());
        let label = if idx == 0 {
            "Init".to_string()
        } else {
            action.unwrap_or_else(|| format!("step {}", idx))
        };
        let changes = match steps.last() {
            Some(prev) => compute_changes(&prev.state, &state, vars),
            None => Vec::new(),
        };
        steps.push(TraceStep {
            label,
            changes,
            state,
        });
    }
    Ok(steps)
}

enum Scope {
    Final,
    All,
    Never,
    Step(usize),
}

struct Assertion {
    scope: Scope,
    expr: Expr,
}

fn parse_assertion(raw: &str) -> Result<Assertion, String> {
    let trimmed = raw.trim();
    if let Some(rest) = strip_keyword(trimmed, "final") {
        return Ok(Assertion {
            scope: Scope::Final,
            expr: parse_pred(rest)?,
        });
    }
    if let Some(rest) = strip_keyword(trimmed, "all") {
        return Ok(Assertion {
            scope: Scope::All,
            expr: parse_pred(rest)?,
        });
    }
    if let Some(rest) = strip_keyword(trimmed, "never") {
        return Ok(Assertion {
            scope: Scope::Never,
            expr: parse_pred(rest)?,
        });
    }
    if let Some(rest) = trimmed.strip_prefix("step ") {
        let (num, expr_text) = rest
            .split_once(':')
            .ok_or_else(|| format!("expected 'step N: <expr>' in {:?}", raw))?;
        let n: usize = num
            .trim()
            .parse()
            .map_err(|_| format!("invalid step index in {:?}", raw))?;
        return Ok(Assertion {
            scope: Scope::Step(n),
            expr: parse_pred(expr_text)?,
        });
    }
    Ok(Assertion {
        scope: Scope::Final,
        expr: parse_pred(trimmed)?,
    })
}

fn strip_keyword<'a>(s: &'a str, kw: &str) -> Option<&'a str> {
    s.strip_prefix(kw)
        .and_then(|r| r.strip_prefix(':'))
        .map(|r| r.trim())
}

fn parse_pred(text: &str) -> Result<Expr, String> {
    parse_expr(text.trim()).map_err(|e| format!("failed to parse '{}': {}", text.trim(), e.message))
}

fn run_assertions(
    raws: &[String],
    states: &[&State],
    vars: &[Arc<str>],
    env: &Env,
    defs: &Definitions,
) -> Vec<AssertionResult> {
    raws.iter()
        .map(|raw| match parse_assertion(raw) {
            Err(e) => AssertionResult {
                raw: raw.clone(),
                passed: false,
                detail: Some(e),
            },
            Ok(assertion) => evaluate_assertion(raw, &assertion, states, vars, env, defs),
        })
        .collect()
}

fn evaluate_assertion(
    raw: &str,
    assertion: &Assertion,
    states: &[&State],
    vars: &[Arc<str>],
    env: &Env,
    defs: &Definitions,
) -> AssertionResult {
    let pass = |detail: Option<String>| AssertionResult {
        raw: raw.to_string(),
        passed: detail.is_none(),
        detail,
    };

    match assertion.scope {
        Scope::Final => match states.last() {
            None => pass(Some("no states in trace".to_string())),
            Some(state) => match eval_pred(&assertion.expr, state, vars, env, defs) {
                Ok(true) => pass(None),
                Ok(false) => pass(Some("false in final state".to_string())),
                Err(e) => pass(Some(e)),
            },
        },
        Scope::All => {
            for (i, state) in states.iter().enumerate() {
                match eval_pred(&assertion.expr, state, vars, env, defs) {
                    Ok(true) => {}
                    Ok(false) => return pass(Some(format!("false at state {}", i))),
                    Err(e) => return pass(Some(e)),
                }
            }
            pass(None)
        }
        Scope::Never => {
            for (i, state) in states.iter().enumerate() {
                match eval_pred(&assertion.expr, state, vars, env, defs) {
                    Ok(false) => {}
                    Ok(true) => return pass(Some(format!("true at state {}", i))),
                    Err(e) => return pass(Some(e)),
                }
            }
            pass(None)
        }
        Scope::Step(n) => match states.get(n) {
            None => pass(Some(format!("trace has no state {}", n))),
            Some(state) => match eval_pred(&assertion.expr, state, vars, env, defs) {
                Ok(true) => pass(None),
                Ok(false) => pass(Some(format!("false at state {}", n))),
                Err(e) => pass(Some(e)),
            },
        },
    }
}

fn eval_pred(
    expr: &Expr,
    state: &State,
    vars: &[Arc<str>],
    env: &Env,
    defs: &Definitions,
) -> Result<bool, String> {
    let mut eval_env = env.clone();
    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = state.values.get(i) {
            eval_env.insert(var.clone(), val.clone());
        }
    }
    match crate::eval::eval(expr, &mut eval_env, defs) {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(other) => Err(format!("not a boolean: {:?}", other)),
        Err(e) => Err(format!("{:?}", e)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::demo::manifest::Manifest;

    fn fixture_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_cases/demo")
    }

    fn load() -> (PathBuf, Manifest) {
        let dir = fixture_dir();
        let manifest = Manifest::load(&dir.join("Counter.demo.json")).expect("manifest loads");
        (dir, manifest)
    }

    fn failures(report: &BeatReport) -> Vec<String> {
        let mut out = Vec::new();
        for run in &report.runs {
            if let Some(f) = &run.failure {
                out.push(format!("{}: {}", run.variant, f));
            }
            for a in &run.assertions {
                if !a.passed {
                    out.push(format!(
                        "{}: {:?} -> {}",
                        run.variant,
                        a.raw,
                        a.detail.clone().unwrap_or_default()
                    ));
                }
            }
        }
        out
    }

    #[test]
    fn manifest_validates() {
        let (_, manifest) = load();
        assert_eq!(manifest.beats.len(), 2);
        assert!(manifest.variants.contains_key("low"));
    }

    #[test]
    fn all_beats_pass() {
        let (dir, manifest) = load();
        for beat in &manifest.beats {
            let report = run_beat(&dir, &manifest, beat);
            assert!(
                report.passed(),
                "beat {:?} failed: {:?}",
                beat.title,
                failures(&report)
            );
        }
    }

    #[test]
    fn compare_beat_runs_both_variants() {
        let (dir, manifest) = load();
        let beat = manifest
            .beats
            .iter()
            .find(|b| !b.compare.is_empty())
            .expect("a compare beat");
        let report = run_beat(&dir, &manifest, beat);
        assert_eq!(report.runs.len(), 2);
    }

    #[test]
    fn wrong_expectation_is_reported() {
        let (dir, mut manifest) = load();
        manifest.beats[0].expect = vec!["final: overflow = TRUE".to_string()];
        let beat = manifest.beats[0].clone();
        let report = run_beat(&dir, &manifest, &beat);
        assert!(!report.passed());
    }
}
