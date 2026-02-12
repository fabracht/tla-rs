#![cfg(feature = "wasm")]

use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::ast::{Env, Value};
use crate::checker::{CheckResult, CheckerConfig, check, format_eval_error, format_trace};
use crate::config::{apply_config, parse_cfg};
use crate::parser::parse;

#[derive(Serialize, Deserialize)]
pub struct WasmCheckResult {
    pub success: bool,
    pub error_type: Option<String>,
    pub error_message: Option<String>,
    pub states_explored: usize,
    pub trace: Option<Vec<String>>,
    pub dot: Option<String>,
}

#[wasm_bindgen]
pub fn check_spec(spec_source: &str, constants_json: &str) -> String {
    let spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ParseError".into()),
                error_message: Some(format!("{:?}", e)),
                states_explored: 0,
                trace: None,
                dot: None,
            })
            .unwrap_or_default();
        }
    };

    let constants: BTreeMap<String, serde_json::Value> =
        serde_json::from_str(constants_json).unwrap_or_default();

    let mut domains = Env::new();
    for (k, v) in constants {
        domains.insert(Arc::from(k), json_to_value(v));
    }

    let config = CheckerConfig::default();
    let result = check(&spec, &domains, &config);

    serde_json::to_string(&result_to_wasm(result, &spec.vars)).unwrap_or_default()
}

#[wasm_bindgen]
pub fn check_spec_with_config(
    spec_source: &str,
    constants_json: &str,
    max_states: usize,
    max_depth: usize,
    allow_deadlock: bool,
    export_dot: bool,
) -> String {
    let spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ParseError".into()),
                error_message: Some(format!("{:?}", e)),
                states_explored: 0,
                trace: None,
                dot: None,
            })
            .unwrap_or_default();
        }
    };

    let constants: BTreeMap<String, serde_json::Value> =
        serde_json::from_str(constants_json).unwrap_or_default();

    let mut domains = Env::new();
    for (k, v) in constants {
        domains.insert(Arc::from(k), json_to_value(v));
    }

    let mut config = CheckerConfig::default();
    config.max_states = max_states;
    config.max_depth = max_depth;
    config.allow_deadlock = allow_deadlock;
    config.export_dot_string = export_dot;

    let result = check(&spec, &domains, &config);

    serde_json::to_string(&result_to_wasm(result, &spec.vars)).unwrap_or_default()
}

#[wasm_bindgen]
pub fn check_spec_with_cfg(
    spec_source: &str,
    cfg_source: &str,
    constants_json: &str,
    max_states: usize,
    max_depth: usize,
    allow_deadlock: bool,
    export_dot: bool,
) -> String {
    let mut spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ParseError".into()),
                error_message: Some(format!("{:?}", e)),
                states_explored: 0,
                trace: None,
                dot: None,
            })
            .unwrap_or_default();
        }
    };

    let cfg = match parse_cfg(cfg_source) {
        Ok(c) => c,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ConfigError".into()),
                error_message: Some(e),
                states_explored: 0,
                trace: None,
                dot: None,
            })
            .unwrap_or_default();
        }
    };

    let constants: BTreeMap<String, serde_json::Value> =
        serde_json::from_str(constants_json).unwrap_or_default();

    let mut domains = Env::new();
    for (k, v) in constants {
        domains.insert(Arc::from(k), json_to_value(v));
    }

    let mut config = CheckerConfig::default();
    config.max_states = max_states;
    config.max_depth = max_depth;
    config.allow_deadlock = allow_deadlock;
    config.export_dot_string = export_dot;

    if let Err(e) = apply_config(&cfg, &mut spec, &mut domains, &mut config, &[], &[], false) {
        return serde_json::to_string(&WasmCheckResult {
            success: false,
            error_type: Some("ConfigError".into()),
            error_message: Some(e),
            states_explored: 0,
            trace: None,
            dot: None,
        })
        .unwrap_or_default();
    }

    let result = check(&spec, &domains, &config);

    serde_json::to_string(&result_to_wasm(result, &spec.vars)).unwrap_or_default()
}

fn json_to_value(v: serde_json::Value) -> Value {
    match v {
        serde_json::Value::Bool(b) => Value::Bool(b),
        serde_json::Value::Number(n) => Value::Int(n.as_i64().unwrap_or(0)),
        serde_json::Value::String(s) => Value::Str(Arc::from(s)),
        serde_json::Value::Array(arr) => {
            let set: std::collections::BTreeSet<Value> =
                arr.into_iter().map(json_to_value).collect();
            Value::Set(set)
        }
        serde_json::Value::Object(obj) => {
            let rec: BTreeMap<Arc<str>, Value> = obj
                .into_iter()
                .map(|(k, v)| (Arc::from(k), json_to_value(v)))
                .collect();
            Value::Record(rec)
        }
        serde_json::Value::Null => Value::Bool(false),
    }
}

fn result_to_wasm(result: CheckResult, vars: &[Arc<str>]) -> WasmCheckResult {
    match result {
        CheckResult::Ok(stats) => WasmCheckResult {
            success: true,
            error_type: None,
            error_message: None,
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
        },
        CheckResult::InvariantViolation(ce, stats) => WasmCheckResult {
            success: false,
            error_type: Some("InvariantViolation".into()),
            error_message: Some(format!("Invariant {} violated", ce.violated_invariant)),
            states_explored: stats.states_explored,
            trace: Some(vec![format_trace(&ce.trace, vars)]),
            dot: stats.dot_graph,
        },
        CheckResult::LivenessViolation(violation, stats) => WasmCheckResult {
            success: false,
            error_type: Some("LivenessViolation".into()),
            error_message: Some(format!(
                "Liveness property violated: {}",
                violation.property
            )),
            states_explored: stats.states_explored,
            trace: Some(vec![
                format_trace(&violation.prefix, vars),
                format_trace(&violation.cycle, vars),
            ]),
            dot: stats.dot_graph,
        },
        CheckResult::Deadlock(trace, _, stats) => WasmCheckResult {
            success: false,
            error_type: Some("Deadlock".into()),
            error_message: Some("Deadlock detected".into()),
            states_explored: stats.states_explored,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: stats.dot_graph,
        },
        CheckResult::InitError(e) => WasmCheckResult {
            success: false,
            error_type: Some("InitError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: None,
            dot: None,
        },
        CheckResult::NextError(e, trace) => WasmCheckResult {
            success: false,
            error_type: Some("NextError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: None,
        },
        CheckResult::InvariantError(e, trace) => WasmCheckResult {
            success: false,
            error_type: Some("InvariantError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: None,
        },
        CheckResult::AssumeViolation(idx) => WasmCheckResult {
            success: false,
            error_type: Some("AssumeViolation".into()),
            error_message: Some(format!("Assume {} violated", idx)),
            states_explored: 0,
            trace: None,
            dot: None,
        },
        CheckResult::AssumeError(idx, e) => WasmCheckResult {
            success: false,
            error_type: Some("AssumeError".into()),
            error_message: Some(format!("Assume {} error: {}", idx, format_eval_error(&e))),
            states_explored: 0,
            trace: None,
            dot: None,
        },
        CheckResult::MaxStatesExceeded(stats) => WasmCheckResult {
            success: false,
            error_type: Some("MaxStatesExceeded".into()),
            error_message: Some(format!("Max states exceeded: {}", stats.states_explored)),
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
        },
        CheckResult::MaxDepthExceeded(stats) => WasmCheckResult {
            success: false,
            error_type: Some("MaxDepthExceeded".into()),
            error_message: Some(format!("Max depth exceeded: {}", stats.max_depth_reached)),
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
        },
        CheckResult::NoInitialStates => WasmCheckResult {
            success: false,
            error_type: Some("NoInitialStates".into()),
            error_message: Some("No initial states found".into()),
            states_explored: 0,
            trace: None,
            dot: None,
        },
        CheckResult::MissingConstants(missing) => WasmCheckResult {
            success: false,
            error_type: Some("MissingConstants".into()),
            error_message: Some(format!(
                "Missing constants: {}",
                missing
                    .iter()
                    .map(|s| s.as_ref())
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            states_explored: 0,
            trace: None,
            dot: None,
        },
    }
}
