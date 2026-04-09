use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::ast::{Env, Spec, Value};
use crate::checker::{
    CheckResult, CheckStats, CheckerConfig, PrepareSpecError, check, format_eval_error,
    format_trace,
};
use crate::config::{apply_config, parse_cfg};
use crate::export::DotMode;
use crate::parser::parse;

#[derive(Serialize, Deserialize, Default)]
struct WasmCheckOptions {
    constants: Option<BTreeMap<String, serde_json::Value>>,
    cfg_source: Option<String>,
    max_states: Option<usize>,
    max_depth: Option<usize>,
    allow_deadlock: Option<bool>,
    export_dot: Option<bool>,
    dot_mode: Option<String>,
}

#[derive(Serialize, Deserialize, Default)]
pub struct WasmCheckResult {
    pub success: bool,
    pub error_type: Option<String>,
    pub error_message: Option<String>,
    pub states_explored: usize,
    pub trace: Option<Vec<String>>,
    pub dot: Option<String>,
    pub warnings: Vec<String>,
}

impl WasmCheckResult {
    fn ok(stats: CheckStats, warnings: Vec<String>) -> Self {
        Self {
            success: true,
            error_type: None,
            error_message: None,
            states_explored: stats.states_explored,
            trace: None,
            dot: stats.dot_graph,
            warnings,
        }
    }

    fn err(error_type: &str, error_message: String, warnings: Vec<String>) -> Self {
        Self {
            success: false,
            error_type: Some(error_type.into()),
            error_message: Some(error_message),
            states_explored: 0,
            trace: None,
            dot: None,
            warnings,
        }
    }

    fn err_with_stats(
        error_type: &str,
        error_message: String,
        stats: CheckStats,
        trace: Option<Vec<String>>,
        warnings: Vec<String>,
    ) -> Self {
        Self {
            success: false,
            error_type: Some(error_type.into()),
            error_message: Some(error_message),
            states_explored: stats.states_explored,
            trace,
            dot: stats.dot_graph,
            warnings,
        }
    }

    fn err_with_trace(
        error_type: &str,
        error_message: String,
        trace: Vec<String>,
        dot: Option<String>,
        warnings: Vec<String>,
    ) -> Self {
        Self {
            success: false,
            error_type: Some(error_type.into()),
            error_message: Some(error_message),
            states_explored: 0,
            trace: Some(trace),
            dot,
            warnings,
        }
    }
}

struct WasmInputs {
    spec: Spec,
    domains: Env,
    config: CheckerConfig,
    warnings: Vec<String>,
}

#[wasm_bindgen]
pub fn check_spec(spec_source: &str, constants_json: &str) -> String {
    let spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => return wasm_error("ParseError", format!("{e:?}")),
    };

    let mut domains = Env::new();
    apply_constants_json(&mut domains, constants_json);

    serde_json::to_string(&check_internal(WasmInputs {
        spec,
        domains,
        config: CheckerConfig::default(),
        warnings: Vec::new(),
    }))
    .unwrap_or_default()
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
        Err(e) => return wasm_error("ParseError", format!("{e:?}")),
    };

    let mut domains = Env::new();
    apply_constants_json(&mut domains, constants_json);

    serde_json::to_string(&check_internal(WasmInputs {
        spec,
        domains,
        config: build_config(max_states, max_depth, allow_deadlock, export_dot),
        warnings: Vec::new(),
    }))
    .unwrap_or_default()
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
        Err(e) => return wasm_error("ParseError", format!("{e:?}")),
    };

    let cfg = match parse_cfg(cfg_source) {
        Ok(c) => c,
        Err(e) => return wasm_error("ConfigError", e),
    };

    let mut domains = Env::new();
    let mut config = build_config(max_states, max_depth, allow_deadlock, export_dot);

    let warnings = match apply_config(
        &cfg,
        &mut spec,
        &mut domains,
        &mut config,
        &[],
        &[],
        allow_deadlock,
    ) {
        Ok(w) => w,
        Err(e) => return wasm_error("ConfigError", e),
    };

    apply_constants_json(&mut domains, constants_json);

    serde_json::to_string(&check_internal(WasmInputs {
        spec,
        domains,
        config,
        warnings,
    }))
    .unwrap_or_default()
}

#[wasm_bindgen]
pub fn check_spec_with_options(spec_source: &str, options_json: &str) -> String {
    let options: WasmCheckOptions = match serde_json::from_str(options_json) {
        Ok(o) => o,
        Err(e) => return wasm_error("OptionsError", format!("Invalid options JSON: {e}")),
    };

    let mut spec = match parse(spec_source) {
        Ok(s) => s,
        Err(e) => return wasm_error("ParseError", format!("{e:?}")),
    };

    let mut domains = Env::new();
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
    if let Some(ref mode_str) = options.dot_mode {
        match mode_str.parse::<DotMode>() {
            Ok(mode) => config.dot_mode = mode,
            Err(e) => return wasm_error("OptionsError", e),
        }
    }

    let mut warnings = Vec::new();
    if let Some(ref cfg_source) = options.cfg_source {
        let cfg = match parse_cfg(cfg_source) {
            Ok(c) => c,
            Err(e) => return wasm_error("ConfigError", e),
        };
        let cli_allow_deadlock = options.allow_deadlock.unwrap_or(false);
        match apply_config(
            &cfg,
            &mut spec,
            &mut domains,
            &mut config,
            &[],
            &[],
            cli_allow_deadlock,
        ) {
            Ok(w) => warnings = w,
            Err(e) => return wasm_error("ConfigError", e),
        }
    }

    if let Some(constants) = options.constants {
        for (k, v) in constants {
            domains.insert(Arc::from(k), json_to_value(v));
        }
    }

    serde_json::to_string(&check_internal(WasmInputs {
        spec,
        domains,
        config,
        warnings,
    }))
    .unwrap_or_default()
}

fn check_internal(inputs: WasmInputs) -> WasmCheckResult {
    let WasmInputs {
        spec,
        domains,
        config,
        warnings,
    } = inputs;
    let result = check(&spec, &domains, &config);
    result_to_wasm(result, &spec.vars, warnings)
}

fn apply_constants_json(domains: &mut Env, constants_json: &str) {
    let constants: BTreeMap<String, serde_json::Value> =
        serde_json::from_str(constants_json).unwrap_or_default();
    for (k, v) in constants {
        domains.insert(Arc::from(k), json_to_value(v));
    }
}

fn wasm_error(error_type: &str, message: String) -> String {
    serde_json::to_string(&WasmCheckResult::err(error_type, message, Vec::new()))
        .unwrap_or_default()
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
        CheckResult::Ok(stats) => WasmCheckResult::ok(stats, warnings),
        CheckResult::InvariantViolation(ce, stats) => WasmCheckResult::err_with_stats(
            "InvariantViolation",
            format!("Invariant {} violated", ce.violated_invariant),
            stats,
            Some(vec![format_trace(&ce.trace, vars)]),
            warnings,
        ),
        CheckResult::LivenessViolation(violation, stats) => WasmCheckResult::err_with_stats(
            "LivenessViolation",
            format!("Liveness property violated: {}", violation.property),
            stats,
            Some(vec![
                format_trace(&violation.prefix, vars),
                format_trace(&violation.cycle, vars),
            ]),
            warnings,
        ),
        CheckResult::Deadlock(trace, _, stats) => WasmCheckResult::err_with_stats(
            "Deadlock",
            "Deadlock detected".into(),
            stats,
            Some(vec![format_trace(&trace, vars)]),
            warnings,
        ),
        CheckResult::InitError(e) => {
            WasmCheckResult::err("InitError", format_eval_error(&e), warnings)
        }
        CheckResult::NextError(e, trace, dot) => WasmCheckResult::err_with_trace(
            "NextError",
            format_eval_error(&e),
            vec![format_trace(&trace, vars)],
            dot,
            warnings,
        ),
        CheckResult::InvariantError(e, trace, dot) => WasmCheckResult::err_with_trace(
            "InvariantError",
            format_eval_error(&e),
            vec![format_trace(&trace, vars)],
            dot,
            warnings,
        ),
        CheckResult::MaxStatesExceeded(stats) => WasmCheckResult::err_with_stats(
            "MaxStatesExceeded",
            format!("Max states exceeded: {}", stats.states_explored),
            stats,
            None,
            warnings,
        ),
        CheckResult::MaxDepthExceeded(stats) => WasmCheckResult::err_with_stats(
            "MaxDepthExceeded",
            format!("Max depth exceeded: {}", stats.max_depth_reached),
            stats,
            None,
            warnings,
        ),
        CheckResult::NoInitialStates => WasmCheckResult::err(
            "NoInitialStates",
            "No initial states found".into(),
            warnings,
        ),
        CheckResult::PrepareError(PrepareSpecError::InstanceError(e)) => {
            WasmCheckResult::err("InstanceError", format_eval_error(&e), warnings)
        }
        CheckResult::PrepareError(PrepareSpecError::MissingConstants(missing)) => {
            WasmCheckResult::err(
                "MissingConstants",
                format!(
                    "Missing constants: {}",
                    missing
                        .iter()
                        .map(|s| s.as_ref())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                warnings,
            )
        }
        CheckResult::PrepareError(PrepareSpecError::AssumeViolation(idx)) => WasmCheckResult::err(
            "AssumeViolation",
            format!("Assume {} violated", idx),
            warnings,
        ),
        CheckResult::PrepareError(PrepareSpecError::AssumeError(idx, e)) => WasmCheckResult::err(
            "AssumeError",
            format!("Assume {} error: {}", idx, format_eval_error(&e)),
            warnings,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const COUNTER_SPEC: &str = "\
VARIABLES count

Init == count = 0

Next == \\/ (count < 3 /\\ count' = count + 1)
        \\/ (count = 3 /\\ count' = 0)

Inv == count >= 0 /\\ count <= 3
";

    const COUNTER_WITH_MAX_SPEC: &str = "\
CONSTANT MAX

VARIABLES count

Init == count = 0

Next == \\/ (count < MAX /\\ count' = count + 1)
        \\/ (count = MAX /\\ count' = 0)

Inv == count >= 0 /\\ count <= MAX
";

    fn parse_result(json: &str) -> WasmCheckResult {
        serde_json::from_str(json).expect("valid JSON result")
    }

    fn run(spec: &str, options: serde_json::Value) -> WasmCheckResult {
        parse_result(&check_spec_with_options(spec, &options.to_string()))
    }

    #[test]
    fn test_check_spec_basic() {
        let result = parse_result(&check_spec(COUNTER_SPEC, "{}"));
        assert!(result.success);
        assert!(result.states_explored > 0);
        assert!(result.error_type.is_none());
    }

    #[test]
    fn test_check_spec_with_options_constants() {
        let options = r#"{"constants": {"MAX": 5}}"#;
        let result = parse_result(&check_spec_with_options(COUNTER_WITH_MAX_SPEC, options));
        assert!(result.success);
        assert!(result.states_explored > 0);
    }

    #[test]
    fn test_check_spec_with_options_cfg_source() {
        let cfg = "CONSTANT MAX = 3\n";
        let options = serde_json::json!({ "cfg_source": cfg }).to_string();
        let result = parse_result(&check_spec_with_options(COUNTER_WITH_MAX_SPEC, &options));
        assert!(result.success);
        assert!(result.states_explored > 0);
    }

    #[test]
    fn test_options_constants_override_cfg() {
        let cfg = "CONSTANT MAX = 2\n";
        let options = serde_json::json!({
            "cfg_source": cfg,
            "constants": {"MAX": 5}
        })
        .to_string();
        let result_override =
            parse_result(&check_spec_with_options(COUNTER_WITH_MAX_SPEC, &options));
        assert!(result_override.success);

        let options_cfg_only = serde_json::json!({ "cfg_source": cfg }).to_string();
        let result_cfg = parse_result(&check_spec_with_options(
            COUNTER_WITH_MAX_SPEC,
            &options_cfg_only,
        ));
        assert!(result_cfg.success);

        assert!(
            result_override.states_explored > result_cfg.states_explored,
            "MAX=5 should produce more states than MAX=2"
        );
    }

    #[test]
    fn test_check_spec_with_options_invalid_json() {
        let result = parse_result(&check_spec_with_options(COUNTER_SPEC, "not json"));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("OptionsError"));
    }

    #[test]
    fn test_check_spec_with_options_export_dot() {
        let options = r#"{"export_dot": true}"#;
        let result = parse_result(&check_spec_with_options(COUNTER_SPEC, options));
        assert!(result.success);
        assert!(result.dot.is_some());
        let dot = result.dot.unwrap();
        assert!(dot.contains("digraph"));
    }

    #[test]
    fn test_invariant_violation() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == count' = count + 1

Inv == count = 0
";
        let result = run(spec, serde_json::json!({"max_states": 10}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("InvariantViolation"));
        assert!(
            result
                .error_message
                .as_deref()
                .unwrap_or("")
                .contains("violated")
        );
    }

    #[test]
    fn test_deadlock() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == count < 0 /\\ count' = count - 1
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("Deadlock"));
        assert!(
            result
                .error_message
                .as_deref()
                .unwrap_or("")
                .contains("Deadlock")
        );
    }

    #[test]
    fn test_init_error() {
        let spec = "\
VARIABLES x

Init == x = 0 /\\ (1 + TRUE) > 0

Next == x' = x
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("InitError"));
    }

    #[test]
    fn test_next_error() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == count' = undefined_var
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("NextError"));
    }

    #[test]
    fn test_invariant_error() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == count' = count + 1

Inv == undefined_var > 0
";
        let result = run(spec, serde_json::json!({"max_states": 10}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("InvariantError"));
    }

    #[test]
    fn test_max_states_exceeded() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == \\/ (count < 1000 /\\ count' = count + 1)
        \\/ (count = 1000 /\\ count' = 0)
";
        let result = run(
            spec,
            serde_json::json!({"max_states": 5, "allow_deadlock": true}),
        );
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("MaxStatesExceeded"));
    }

    #[test]
    fn test_max_depth_exceeded() {
        let spec = "\
VARIABLES count

Init == count = 0

Next == count' = count + 1
";
        let result = run(
            spec,
            serde_json::json!({"max_depth": 2, "allow_deadlock": true}),
        );
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("MaxDepthExceeded"));
    }

    #[test]
    fn test_no_initial_states() {
        let spec = "\
VARIABLES x

Init == FALSE

Next == x' = x
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("NoInitialStates"));
    }

    #[test]
    fn test_missing_constants() {
        let spec = "\
CONSTANT MAX

VARIABLES count

Init == count = 0

Next == count' = (count + 1) % MAX
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("MissingConstants"));
        assert!(
            result
                .error_message
                .as_deref()
                .unwrap_or("")
                .contains("MAX")
        );
    }

    #[test]
    fn test_assume_violation() {
        let spec = "\
VARIABLES x

ASSUME 1 = 2

Init == x = 0

Next == x' = x
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("AssumeViolation"));
    }

    #[test]
    fn test_assume_error() {
        let spec = "\
VARIABLES x

ASSUME undefined_const > 0

Init == x = 0

Next == x' = x
";
        let result = run(spec, serde_json::json!({}));
        assert!(!result.success);
        assert_eq!(result.error_type.as_deref(), Some("AssumeError"));
    }
}
