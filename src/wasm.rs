use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::ast::{Env, Value};
use crate::checker::{CheckResult, CheckerConfig, check, format_eval_error, format_trace};
use crate::config::{apply_config, parse_cfg};
use crate::parser::parse;

#[derive(Serialize, Deserialize, Default)]
struct WasmCheckOptions {
    constants: Option<BTreeMap<String, serde_json::Value>>,
    cfg_source: Option<String>,
    max_states: Option<usize>,
    max_depth: Option<usize>,
    allow_deadlock: Option<bool>,
    export_dot: Option<bool>,
}

#[derive(Serialize, Deserialize)]
pub struct WasmCheckResult {
    pub success: bool,
    pub error_type: Option<String>,
    pub error_message: Option<String>,
    pub states_explored: usize,
    pub trace: Option<Vec<String>>,
    pub dot: Option<String>,
    pub warnings: Vec<String>,
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
                warnings: vec![],
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

    serde_json::to_string(&result_to_wasm(result, &spec.vars, vec![])).unwrap_or_default()
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
                warnings: vec![],
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

    let config = build_config(max_states, max_depth, allow_deadlock, export_dot);

    let result = check(&spec, &domains, &config);

    serde_json::to_string(&result_to_wasm(result, &spec.vars, vec![])).unwrap_or_default()
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
                warnings: vec![],
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
                warnings: vec![],
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

    let mut config = build_config(max_states, max_depth, allow_deadlock, export_dot);

    let warnings = match apply_config(&cfg, &mut spec, &mut domains, &mut config, &[], &[], false) {
        Ok(w) => w,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ConfigError".into()),
                error_message: Some(e),
                states_explored: 0,
                trace: None,
                dot: None,
                warnings: vec![],
            })
            .unwrap_or_default();
        }
    };

    let result = check(&spec, &domains, &config);

    serde_json::to_string(&result_to_wasm(result, &spec.vars, warnings)).unwrap_or_default()
}

#[wasm_bindgen]
pub fn check_spec_with_options(spec_source: &str, options_json: &str) -> String {
    let options: WasmCheckOptions = match serde_json::from_str(options_json) {
        Ok(o) => o,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("OptionsError".into()),
                error_message: Some(format!("Invalid options JSON: {e}")),
                states_explored: 0,
                trace: None,
                dot: None,
                warnings: vec![],
            })
            .unwrap_or_default();
        }
    };

    let mut spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => {
            return serde_json::to_string(&WasmCheckResult {
                success: false,
                error_type: Some("ParseError".into()),
                error_message: Some(format!("{e:?}")),
                states_explored: 0,
                trace: None,
                dot: None,
                warnings: vec![],
            })
            .unwrap_or_default();
        }
    };

    let mut domains = Env::new();
    if let Some(constants) = options.constants {
        for (k, v) in constants {
            domains.insert(Arc::from(k), json_to_value(v));
        }
    }

    let mut config = CheckerConfig::default();
    if let Some(v) = options.max_states {
        config.max_states = v;
    }
    if let Some(v) = options.max_depth {
        config.max_depth = v;
    }
    if let Some(v) = options.allow_deadlock {
        config.allow_deadlock = v;
    }
    if let Some(v) = options.export_dot {
        config.export_dot_string = v;
    }

    let mut warnings = Vec::new();
    if let Some(ref cfg_source) = options.cfg_source {
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
                    warnings: vec![],
                })
                .unwrap_or_default();
            }
        };
        match apply_config(&cfg, &mut spec, &mut domains, &mut config, &[], &[], false) {
            Ok(w) => warnings = w,
            Err(e) => {
                return serde_json::to_string(&WasmCheckResult {
                    success: false,
                    error_type: Some("ConfigError".into()),
                    error_message: Some(e),
                    states_explored: 0,
                    trace: None,
                    dot: None,
                    warnings: vec![],
                })
                .unwrap_or_default();
            }
        }
    }

    let result = check(&spec, &domains, &config);
    serde_json::to_string(&result_to_wasm(result, &spec.vars, warnings)).unwrap_or_default()
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

fn build_config(
    max_states: usize,
    max_depth: usize,
    allow_deadlock: bool,
    export_dot: bool,
) -> CheckerConfig {
    CheckerConfig {
        max_states,
        max_depth,
        allow_deadlock,
        export_dot_string: export_dot,
        ..Default::default()
    }
}

fn result_to_wasm(
    result: CheckResult,
    vars: &[Arc<str>],
    warnings: Vec<String>,
) -> WasmCheckResult {
    match result {
        CheckResult::Ok(stats) => WasmCheckResult {
            success: true,
            error_type: None,
            error_message: None,
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
            warnings,
        },
        CheckResult::InvariantViolation(ce, stats) => WasmCheckResult {
            success: false,
            error_type: Some("InvariantViolation".into()),
            error_message: Some(format!("Invariant {} violated", ce.violated_invariant)),
            states_explored: stats.states_explored,
            trace: Some(vec![format_trace(&ce.trace, vars)]),
            dot: stats.dot_graph,
            warnings,
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
            warnings,
        },
        CheckResult::Deadlock(trace, _, stats) => WasmCheckResult {
            success: false,
            error_type: Some("Deadlock".into()),
            error_message: Some("Deadlock detected".into()),
            states_explored: stats.states_explored,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: stats.dot_graph,
            warnings,
        },
        CheckResult::InitError(e) => WasmCheckResult {
            success: false,
            error_type: Some("InitError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: None,
            dot: None,
            warnings,
        },
        CheckResult::NextError(e, trace) => WasmCheckResult {
            success: false,
            error_type: Some("NextError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: None,
            warnings,
        },
        CheckResult::InvariantError(e, trace) => WasmCheckResult {
            success: false,
            error_type: Some("InvariantError".into()),
            error_message: Some(format_eval_error(&e)),
            states_explored: 0,
            trace: Some(vec![format_trace(&trace, vars)]),
            dot: None,
            warnings,
        },
        CheckResult::AssumeViolation(idx) => WasmCheckResult {
            success: false,
            error_type: Some("AssumeViolation".into()),
            error_message: Some(format!("Assume {} violated", idx)),
            states_explored: 0,
            trace: None,
            dot: None,
            warnings,
        },
        CheckResult::AssumeError(idx, e) => WasmCheckResult {
            success: false,
            error_type: Some("AssumeError".into()),
            error_message: Some(format!("Assume {} error: {}", idx, format_eval_error(&e))),
            states_explored: 0,
            trace: None,
            dot: None,
            warnings,
        },
        CheckResult::MaxStatesExceeded(stats) => WasmCheckResult {
            success: false,
            error_type: Some("MaxStatesExceeded".into()),
            error_message: Some(format!("Max states exceeded: {}", stats.states_explored)),
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
            warnings,
        },
        CheckResult::MaxDepthExceeded(stats) => WasmCheckResult {
            success: false,
            error_type: Some("MaxDepthExceeded".into()),
            error_message: Some(format!("Max depth exceeded: {}", stats.max_depth_reached)),
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
            warnings,
        },
        CheckResult::NoInitialStates => WasmCheckResult {
            success: false,
            error_type: Some("NoInitialStates".into()),
            error_message: Some("No initial states found".into()),
            states_explored: 0,
            trace: None,
            dot: None,
            warnings,
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
            warnings,
        },
    }
}
