//! TLC-confirmed liveness oracle.
//!
//! Every case in `tests/liveness_corpus/manifest.json` carries a verdict obtained by
//! running real TLC (`scripts/liveness-oracle.sh` re-derives them locally). This test
//! needs no Java: it runs tla-rs on each case and compares against the recorded
//! verdict. Cases marked `xfail_until_phase` document known divergences and must still
//! diverge; once one starts agreeing with TLC its xfail marker has to be removed. A
//! divergence may be an error or a false alarm, but never a false pass: an xfail case
//! that TLC reports as violated fails the test if tla-rs reports it ok.
//! Every violation reported on a non-xfail case is re-validated by an independent
//! lasso evaluator (`lasso.rs`).

#[path = "liveness_oracle/lasso.rs"]
mod lasso;

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value as Json;
use tla_checker::ast::{Env, Expr, State};
use tla_checker::checker::{CheckResult, check, prepare_spec};
use tla_checker::config::parse_cfg;
use tla_checker::load::{Prepared, prepare_from_path};

use lasso::{Lasso, Model};

struct Case {
    id: String,
    spec: PathBuf,
    cfg: PathBuf,
    expected: String,
    kind: Option<String>,
    xfail: Option<String>,
}

enum Counterexample {
    Lasso(Vec<State>, Vec<State>),
    Trace(Vec<State>),
}

struct Observed {
    verdict: &'static str,
    kind: Option<&'static str>,
    detail: String,
    counterexample: Option<Counterexample>,
}

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/liveness_corpus")
}

fn json_str(entry: &Json, field: &str) -> Option<String> {
    entry.get(field).and_then(Json::as_str).map(str::to_string)
}

fn load_cases() -> Vec<Case> {
    let dir = corpus_dir();
    let text = fs::read_to_string(dir.join("manifest.json")).expect("manifest readable");
    let entries: Vec<Json> = serde_json::from_str(&text).expect("manifest is a JSON array");
    entries
        .iter()
        .map(|entry| {
            let id = json_str(entry, "id").expect("case id");
            Case {
                spec: dir.join(json_str(entry, "spec").expect("case spec")),
                cfg: dir.join(json_str(entry, "cfg").expect("case cfg")),
                expected: json_str(entry, "expected").expect("case expected"),
                kind: json_str(entry, "kind"),
                xfail: json_str(entry, "xfail_until_phase"),
                id,
            }
        })
        .collect()
}

fn prepare(case: &Case) -> Prepared {
    prepare_from_path(&case.spec, Some(&case.cfg), &[])
        .unwrap_or_else(|e| panic!("{}: failed to prepare: {e}", case.id))
}

fn observe(case: &Case) -> Observed {
    let prepared = match prepare_from_path(&case.spec, Some(&case.cfg), &[]) {
        Ok(prepared) => prepared,
        Err(e) => {
            return Observed {
                verdict: "error",
                kind: None,
                detail: format!("load error: {e}").chars().take(160).collect(),
                counterexample: None,
            };
        }
    };
    let mut config = prepared.checker_config;
    config.check_liveness = true;
    match check(&prepared.spec, &prepared.domains, &config) {
        CheckResult::Ok(_) => Observed {
            verdict: "ok",
            kind: None,
            detail: String::new(),
            counterexample: None,
        },
        CheckResult::LivenessViolation(violation, _) => Observed {
            verdict: "violated",
            kind: Some("liveness"),
            detail: violation.property.clone(),
            counterexample: Some(Counterexample::Lasso(violation.prefix, violation.cycle)),
        },
        CheckResult::InvariantViolation(counterexample, _) => Observed {
            verdict: "violated",
            kind: Some("invariant"),
            detail: format!("invariant #{}", counterexample.violated_invariant),
            counterexample: Some(Counterexample::Trace(counterexample.trace)),
        },
        other => Observed {
            verdict: "error",
            kind: None,
            detail: format!("{other:?}").chars().take(160).collect(),
            counterexample: None,
        },
    }
}

fn definition(defs: &tla_checker::eval::Definitions, name: &str) -> Result<Expr, String> {
    defs.get(name)
        .map(|(_, body)| body.as_ref().clone())
        .ok_or_else(|| format!("definition {name} not found"))
}

fn validate(case: &Case, counterexample: &Counterexample) -> Result<(), String> {
    let prepared = prepare(case);
    let cfg_text = fs::read_to_string(&case.cfg).map_err(|e| e.to_string())?;
    let cfg = parse_cfg(&cfg_text)?;
    let (constants, defs) = prepare_spec(&prepared.spec, &prepared.domains, Some(&case.spec), true)
        .map_err(|e| format!("prepare_spec failed: {e:?}"))?;
    let init = prepared.spec.init.clone().ok_or("spec has no Init")?;
    let next = prepared.spec.next.clone().ok_or("spec has no Next")?;
    let property_name = cfg.properties.first().ok_or("cfg has no PROPERTY")?;
    let property = definition(&defs, property_name)?;
    let model = Model {
        vars: &prepared.spec.vars,
        constants: &constants,
        defs: &defs,
    };
    let empty = Env::new();
    match counterexample {
        Counterexample::Lasso(prefix, cycle) => {
            let lasso = Lasso::from_prefix_and_cycle(prefix, cycle)?;
            model.check_is_behavior(&lasso, &init, &next)?;
            if let Some(spec_name) = &cfg.specification {
                let formula = definition(&defs, spec_name)?;
                if !model.holds(&lasso, &formula, 0, &empty)? {
                    return Err(format!(
                        "lasso is not a behavior of {spec_name} (fairness or a spec conjunct fails)"
                    ));
                }
            }
            if model.holds(&lasso, &property, 0, &empty)? {
                return Err(format!("{property_name} is TRUE on the reported lasso"));
            }
        }
        Counterexample::Trace(trace) => {
            let lasso = Lasso::stuttering_after(trace)?;
            model.check_is_behavior(&lasso, &init, &next)?;
            if model.holds(&lasso, &property, 0, &empty)? {
                return Err(format!(
                    "{property_name} is TRUE on the reported trace extended by stuttering"
                ));
            }
        }
    }
    Ok(())
}

#[test]
fn liveness_corpus_matches_tlc() {
    let cases = load_cases();
    assert!(!cases.is_empty(), "manifest has no cases");
    let mut rows = Vec::new();
    let mut failures = 0usize;
    for case in &cases {
        if case.expected == "tlc_unsupported" {
            rows.push(format!(
                "{:<6} {:<26} {:<26} {:<5} SKIP (TLC unsupported)",
                case.id, "-", "-", "-"
            ));
            continue;
        }
        let observed = observe(case);
        let agrees = observed.verdict == case.expected
            && (observed.verdict != "violated" || observed.kind == case.kind.as_deref());
        let status = match (&case.xfail, agrees) {
            (None, true) => match (&observed.counterexample, observed.verdict) {
                (Some(cex), "violated") => match validate(case, cex) {
                    Ok(()) => "PASS (counterexample validated)".to_string(),
                    Err(reason) => {
                        failures += 1;
                        format!("FAIL: invalid counterexample: {reason}")
                    }
                },
                _ => "PASS".to_string(),
            },
            (None, false) => {
                failures += 1;
                format!("FAIL: disagrees with TLC {}", observed.detail)
            }
            (Some(_), false) if case.expected == "violated" && observed.verdict == "ok" => {
                failures += 1;
                "FAIL: false pass — an xfail case may be rejected or misreported, never reported ok"
                    .to_string()
            }
            (Some(_), false) => match (&observed.counterexample, case.expected.as_str()) {
                (Some(cex), "ok") => match validate(case, cex) {
                    Err(_) => "XFAIL (validator rejects the false alarm)".to_string(),
                    Ok(()) => {
                        failures += 1;
                        "FAIL: lasso validator accepts a counterexample TLC refutes".to_string()
                    }
                },
                _ => "XFAIL".to_string(),
            },
            (Some(phase), true) => {
                failures += 1;
                format!(
                    "FAIL: now agrees with TLC; remove xfail_until_phase \"{phase}\" from {} in manifest.json",
                    case.id
                )
            }
        };
        rows.push(format!(
            "{:<6} {:<26} {:<26} {:<5} {}",
            case.id,
            format!("{}/{}", case.expected, case.kind.as_deref().unwrap_or("-")),
            format!("{}/{}", observed.verdict, observed.kind.unwrap_or("-")),
            case.xfail.as_deref().unwrap_or("-"),
            status
        ));
    }
    let header = format!(
        "{:<6} {:<26} {:<26} {:<5} status",
        "id", "expected (TLC)", "tla-rs now", "xfail"
    );
    let table = format!("{header}\n{}", rows.join("\n"));
    println!("{table}");
    if failures > 0 {
        panic!("{failures} liveness oracle case(s) failed\n{table}");
    }
}
