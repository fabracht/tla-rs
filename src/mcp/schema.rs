use std::collections::BTreeMap;
use std::sync::Arc;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::ast::{State, Value};
use crate::checker::format_value;
use crate::eval::EvalError;
use crate::source::Source;
use crate::span::Span;

use super::SCHEMA_VERSION;

fn schema_version_default() -> String {
    SCHEMA_VERSION.to_string()
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ValidateSpecInput {
    pub spec_path: String,
    #[serde(default)]
    pub constants: BTreeMap<String, String>,
    #[serde(default)]
    pub config_path: Option<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ValidateSpecOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: ValidationStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub spec: Option<SpecSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ParseWarning>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

impl ValidateSpecOutput {
    pub fn ok(spec: SpecSummary, warnings: Vec<ParseWarning>) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ValidationStatus::Ok,
            spec: Some(spec),
            warnings,
            error: None,
        }
    }

    pub fn error(error: StructuredError) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ValidationStatus::Error,
            spec: None,
            warnings: Vec::new(),
            error: Some(error),
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone)]
pub struct ParseWarning {
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<SourceSpan>,
}

impl ParseWarning {
    pub fn from_spanned(spanned: &crate::span::Spanned<String>, source: &Source) -> Self {
        let span = if spanned.span.is_empty() {
            None
        } else {
            Some(SourceSpan::from_span(spanned.span, source))
        };
        Self {
            message: spanned.value.clone(),
            span,
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum ValidationStatus {
    Ok,
    Error,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct SpecSummary {
    pub vars: Vec<String>,
    pub constants: Vec<ConstantBinding>,
    pub invariants: Vec<InvariantSummary>,
    pub has_init: bool,
    pub has_next: bool,
    pub definition_count: usize,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ConstantBinding {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<TlaValue>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ListInvariantsInput {
    pub spec_path: String,
    #[serde(default)]
    pub constants: BTreeMap<String, String>,
    #[serde(default)]
    pub config_path: Option<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ListInvariantsOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: ValidationStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub invariants: Vec<InvariantSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ParseWarning>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

impl ListInvariantsOutput {
    pub fn ok(invariants: Vec<InvariantSummary>, warnings: Vec<ParseWarning>) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ValidationStatus::Ok,
            invariants,
            warnings,
            error: None,
        }
    }

    pub fn error(error: StructuredError) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ValidationStatus::Error,
            invariants: Vec::new(),
            warnings: Vec::new(),
            error: Some(error),
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone)]
pub struct InvariantSummary {
    pub name: Option<String>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct CheckSpecInput {
    pub spec_path: String,
    pub max_states: u64,
    pub max_depth: u64,
    pub max_seconds: u64,
    #[serde(default)]
    pub constants: BTreeMap<String, String>,
    #[serde(default)]
    pub symmetry: Option<String>,
    #[serde(default)]
    pub allow_deadlock: Option<bool>,
    #[serde(default)]
    pub check_liveness: Option<bool>,
    #[serde(default)]
    pub count_satisfying: Vec<String>,
    #[serde(default)]
    pub continue_on_violation: bool,
    #[serde(default)]
    pub state_constraint: Option<String>,
    #[serde(default)]
    pub config_path: Option<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct CheckSpecOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub advisories: Vec<String>,
    #[serde(flatten)]
    pub outcome: CheckOutcome,
}

impl CheckSpecOutput {
    pub fn new(outcome: CheckOutcome) -> Self {
        Self {
            schema_version: schema_version_default(),
            advisories: Vec::new(),
            outcome,
        }
    }

    pub fn with_advisories(mut self, advisories: Vec<String>) -> Self {
        self.advisories = advisories;
        self
    }
}

#[derive(Serialize, JsonSchema, Debug)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum CheckOutcome {
    Ok {
        stats: CheckStatsSummary,
    },
    InvariantViolation {
        invariant: Option<String>,
        trace: Vec<StateSnapshot>,
        actions: Vec<Option<String>>,
        stats: CheckStatsSummary,
    },
    Deadlock {
        trace: Vec<StateSnapshot>,
        actions: Vec<Option<String>>,
        stats: CheckStatsSummary,
    },
    LivenessViolation {
        property: String,
        prefix: Vec<StateSnapshot>,
        cycle: Vec<StateSnapshot>,
        stats: CheckStatsSummary,
    },
    LimitReached {
        limit: LimitKind,
        stats: CheckStatsSummary,
    },
    Error {
        phase: ErrorPhase,
        error: StructuredError,
        #[serde(skip_serializing_if = "Option::is_none")]
        partial_stats: Option<CheckStatsSummary>,
    },
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum LimitKind {
    MaxStates,
    MaxDepth,
    MaxSeconds,
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum ErrorPhase {
    Parse,
    Config,
    Constant,
    Init,
    Next,
    Invariant,
    Io,
    Internal,
}

#[derive(Serialize, JsonSchema, Debug, Default)]
pub struct CheckStatsSummary {
    pub states_explored: u64,
    pub transitions: u64,
    pub max_depth_reached: u64,
    pub elapsed_secs: f64,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub actions: Vec<ActionSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub property_stats: Vec<PropertySummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violation_count: Option<u64>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ActionSummary {
    pub name: Option<String>,
    pub transitions: u64,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct PropertySummary {
    pub name: String,
    pub satisfied: u64,
    pub violated: u64,
    pub errors: u64,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ReplayScenarioInput {
    pub spec_path: String,
    pub scenario: String,
    #[serde(default)]
    pub constants: BTreeMap<String, String>,
    #[serde(default)]
    pub config_path: Option<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ReplayScenarioOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: ScenarioStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub trace: Vec<ScenarioTraceState>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure: Option<ScenarioFailureInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

impl ReplayScenarioOutput {
    pub fn ok(trace: Vec<ScenarioTraceState>) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ScenarioStatus::Ok,
            trace,
            failure: None,
            error: None,
        }
    }

    pub fn failed(trace: Vec<ScenarioTraceState>, failure: ScenarioFailureInfo) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ScenarioStatus::Failed,
            trace,
            failure: Some(failure),
            error: None,
        }
    }

    pub fn error(error: StructuredError) -> Self {
        Self {
            schema_version: schema_version_default(),
            status: ScenarioStatus::Error,
            trace: Vec::new(),
            failure: None,
            error: Some(error),
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum ScenarioStatus {
    Ok,
    Failed,
    Error,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ScenarioTraceState {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_index: Option<usize>,
    pub state: StateSnapshot,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub changes: Vec<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ScenarioFailureInfo {
    pub step_index: usize,
    pub message: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub available_actions: Vec<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct StateSnapshot {
    pub vars: BTreeMap<String, TlaValue>,
}

impl StateSnapshot {
    pub fn from_state(state: &State, var_names: &[Arc<str>]) -> Self {
        let mut vars = BTreeMap::new();
        for (idx, name) in var_names.iter().enumerate() {
            if let Some(val) = state.values.get(idx) {
                vars.insert(name.to_string(), TlaValue::from_value(val));
            }
        }
        Self { vars }
    }
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct TlaValue {
    pub display: String,
    pub json: serde_json::Value,
}

impl TlaValue {
    pub fn from_value(value: &Value) -> Self {
        Self {
            display: format_value(value),
            json: value_to_json(value),
        }
    }
}

fn value_to_json(value: &Value) -> serde_json::Value {
    use serde_json::{Map, Value as J};
    match value {
        Value::Bool(b) => J::Bool(*b),
        Value::Int(i) => J::Number((*i).into()),
        Value::Str(s) => J::String(s.to_string()),
        Value::Set(elems) => {
            let arr = elems.iter().map(value_to_json).collect();
            let mut obj = Map::new();
            obj.insert("kind".into(), J::String("set".into()));
            obj.insert("elements".into(), J::Array(arr));
            J::Object(obj)
        }
        Value::Tuple(elems) => {
            let arr = elems.iter().map(value_to_json).collect();
            let mut obj = Map::new();
            obj.insert("kind".into(), J::String("tuple".into()));
            obj.insert("elements".into(), J::Array(arr));
            J::Object(obj)
        }
        Value::Record(fields) => {
            let mut field_map = Map::new();
            for (k, v) in fields {
                field_map.insert(k.to_string(), value_to_json(v));
            }
            let mut obj = Map::new();
            obj.insert("kind".into(), J::String("record".into()));
            obj.insert("fields".into(), J::Object(field_map));
            J::Object(obj)
        }
        Value::Fn(entries) => {
            let arr = entries
                .iter()
                .map(|(k, v)| {
                    let mut entry = Map::new();
                    entry.insert("key".into(), value_to_json(k));
                    entry.insert("value".into(), value_to_json(v));
                    J::Object(entry)
                })
                .collect();
            let mut obj = Map::new();
            obj.insert("kind".into(), J::String("fn".into()));
            obj.insert("entries".into(), J::Array(arr));
            J::Object(obj)
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone)]
pub struct StructuredError {
    pub kind: ErrorKind,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<SourceSpan>,
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum ErrorKind {
    Io,
    Parse,
    Config,
    Constant,
    Eval,
    Internal,
}

impl StructuredError {
    pub fn io(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Io,
            message: message.into(),
            suggestion: None,
            span: None,
        }
    }

    pub fn parse(message: impl Into<String>, span: Option<SourceSpan>) -> Self {
        Self {
            kind: ErrorKind::Parse,
            message: message.into(),
            suggestion: None,
            span,
        }
    }

    pub fn config(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Config,
            message: message.into(),
            suggestion: None,
            span: None,
        }
    }

    pub fn constant(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Constant,
            message: message.into(),
            suggestion: None,
            span: None,
        }
    }

    pub fn from_eval(err: &EvalError, source: Option<&Source>) -> Self {
        let message = crate::checker::format_eval_error(err);
        let suggestion = match err {
            EvalError::UndefinedVar { suggestion, .. } => {
                suggestion.as_ref().map(|s| s.to_string())
            }
            _ => None,
        };
        let span = match err {
            EvalError::UndefinedVar { span, .. }
            | EvalError::TypeMismatch { span, .. }
            | EvalError::DivisionByZero { span }
            | EvalError::EmptyChoose { span }
            | EvalError::DomainError { span, .. } => *span,
        };
        let source_span = span
            .filter(|s| !s.is_empty())
            .and_then(|s| source.map(|src| SourceSpan::from_span(s, src)));
        Self {
            kind: ErrorKind::Eval,
            message,
            suggestion,
            span: source_span,
        }
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self {
            kind: ErrorKind::Internal,
            message: message.into(),
            suggestion: None,
            span: None,
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, Clone, Copy)]
pub struct SourceSpan {
    pub start_offset: u32,
    pub end_offset: u32,
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

impl SourceSpan {
    pub fn from_span(span: Span, source: &Source) -> Self {
        let (start_line, start_column) = source.line_col(span.start);
        let (end_line, end_column) = source.line_col(span.end);
        Self {
            start_offset: span.start,
            end_offset: span.end,
            start_line: start_line as u32,
            start_column: start_column as u32,
            end_line: end_line as u32,
            end_column: end_column as u32,
        }
    }
}

#[derive(Serialize, JsonSchema, Debug, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum DemoStatus {
    Passed,
    Failed,
    Error,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct AssertionSummary {
    pub expectation: String,
    pub passed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct DemoTraceState {
    pub label: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub changes: Vec<String>,
    pub state: StateSnapshot,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct VariantRunSummary {
    pub variant: String,
    pub passed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub assertions: Vec<AssertionSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub trace: Vec<DemoTraceState>,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct BeatSummary {
    pub index: usize,
    pub title: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    pub passed: bool,
    pub runs: Vec<VariantRunSummary>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ValidateDemoInput {
    pub manifest_path: String,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ValidateDemoOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: DemoStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub beats: Vec<BeatSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct AppendBeatInput {
    pub manifest_path: String,
    pub title: String,
    #[serde(default)]
    pub variant: Option<String>,
    #[serde(default)]
    pub compare: Vec<String>,
    pub scenario: Vec<String>,
    #[serde(default)]
    pub note: Option<String>,
    #[serde(default)]
    pub expect: Vec<String>,
    #[serde(default)]
    pub expect_per_variant: BTreeMap<String, Vec<String>>,
    #[serde(default)]
    pub validate_only: bool,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct AppendBeatOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: DemoStatus,
    pub written: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub beat: Option<BeatSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ExportDemoDocInput {
    pub manifest_path: String,
    pub out_path: String,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ExportDemoDocOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: DemoStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub written_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

#[derive(Deserialize, JsonSchema, Debug, Clone)]
pub struct ExportDemoHtmlInput {
    pub manifest_path: String,
    pub out_path: String,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct ExportDemoHtmlOutput {
    #[serde(default = "schema_version_default")]
    pub schema_version: String,
    pub status: DemoStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub written_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<StructuredError>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use schemars::schema_for;
    use serde::Serialize;
    use serde_json::Value;

    fn required(schema: &Value) -> Vec<String> {
        schema
            .get("required")
            .and_then(|r| r.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default()
    }

    fn keys(value: &Value) -> Vec<String> {
        match value {
            Value::Object(m) => m.keys().cloned().collect(),
            _ => Vec::new(),
        }
    }

    fn assert_required_present<T: JsonSchema>(label: &str, sample: &impl Serialize) {
        let schema = serde_json::to_value(schema_for!(T)).unwrap();
        let serialized = serde_json::to_value(sample).unwrap();
        let present = keys(&serialized);
        let req = required(&schema);
        let missing: Vec<&String> = req.iter().filter(|r| !present.contains(r)).collect();
        assert!(
            missing.is_empty(),
            "{label}: schema marks {missing:?} required but a minimal response omits them \
             (a strict MCP client rejects this with -32602)"
        );
    }

    #[test]
    fn empty_stats_satisfies_its_schema() {
        assert_required_present::<CheckStatsSummary>(
            "CheckStatsSummary",
            &CheckStatsSummary::default(),
        );
    }

    #[test]
    fn passing_outcome_matches_its_oneof_branch() {
        let outcome = CheckOutcome::Ok {
            stats: CheckStatsSummary::default(),
        };
        let serialized = serde_json::to_value(&outcome).unwrap();
        let schema = serde_json::to_value(schema_for!(CheckOutcome)).unwrap();
        let branch = schema
            .get("oneOf")
            .and_then(|o| o.as_array())
            .and_then(|branches| {
                branches.iter().find(|b| {
                    b.get("properties")
                        .and_then(|p| p.get("status"))
                        .and_then(|s| s.get("const"))
                        .and_then(|c| c.as_str())
                        == Some("ok")
                })
            })
            .expect("ok branch present in CheckOutcome oneOf");
        let present = keys(&serialized);
        let req = required(branch);
        let missing: Vec<&String> = req.iter().filter(|r| !present.contains(r)).collect();
        assert!(
            missing.is_empty(),
            "ok outcome omits schema-required fields {missing:?}"
        );
    }
}
