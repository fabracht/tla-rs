use std::collections::VecDeque;
#[cfg(not(target_arch = "wasm32"))]
use std::fs::File;
#[cfg(not(target_arch = "wasm32"))]
use std::io::BufWriter;
#[cfg(not(target_arch = "wasm32"))]
use std::path::PathBuf;
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use indexmap::IndexSet;

use crate::ast::{Env, Expr, Spec, State, Value};
use crate::eval::{eval, eval_with_context, init_states, make_primed_names, next_states, update_checker_stats, set_resolved_instances, CheckerStats as EvalCheckerStats, Definitions, EvalContext, EvalError};
use crate::modules::{resolve_instances, ModuleRegistry};
#[cfg(not(target_arch = "wasm32"))]
use crate::export::export_dot;
use crate::graph::StateGraph;
use crate::liveness::{self, LivenessViolation};
use crate::scc::compute_sccs;
use crate::stdlib;
use crate::symmetry::SymmetryConfig;

#[derive(Debug)]
pub struct CheckerConfig {
    pub max_states: usize,
    pub max_depth: usize,
    pub symmetric_constants: Vec<Arc<str>>,
    #[cfg(not(target_arch = "wasm32"))]
    pub export_dot_path: Option<PathBuf>,
    pub allow_deadlock: bool,
    pub check_liveness: bool,
    pub quiet: bool,
    pub quick_mode: bool,
    pub verbosity: u8,
    pub json_output: bool,
    #[cfg(not(target_arch = "wasm32"))]
    pub spec_path: Option<PathBuf>,
    #[cfg(not(target_arch = "wasm32"))]
    pub trace_json_path: Option<PathBuf>,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            max_states: 1_000_000,
            max_depth: 100,
            symmetric_constants: Vec::new(),
            #[cfg(not(target_arch = "wasm32"))]
            export_dot_path: None,
            allow_deadlock: false,
            check_liveness: false,
            quiet: false,
            quick_mode: false,
            verbosity: 1,
            json_output: false,
            #[cfg(not(target_arch = "wasm32"))]
            spec_path: None,
            #[cfg(not(target_arch = "wasm32"))]
            trace_json_path: None,
        }
    }
}

impl CheckerConfig {
    pub fn new() -> Self {
        Self::default()
    }
}

fn format_eta(secs: f64) -> String {
    if secs.is_nan() || secs.is_infinite() || secs < 0.0 {
        return "N/A".to_string();
    }
    let secs = secs as u64;
    if secs < 60 {
        format!("{}s", secs)
    } else if secs < 3600 {
        format!("{}m{}s", secs / 60, secs % 60)
    } else {
        format!("{}h{}m", secs / 3600, (secs % 3600) / 60)
    }
}

#[derive(Debug)]
pub struct Counterexample {
    pub trace: Vec<State>,
    pub violated_invariant: usize,
}

#[derive(Debug)]
pub struct CheckStats {
    pub states_explored: usize,
    pub transitions: usize,
    pub max_depth_reached: usize,
    pub elapsed_secs: f64,
}

#[derive(Debug)]
pub enum CheckResult {
    Ok(CheckStats),
    InvariantViolation(Counterexample, CheckStats),
    LivenessViolation(LivenessViolation, CheckStats),
    Deadlock(Vec<State>, CheckStats),
    InitError(EvalError),
    NextError(EvalError, Vec<State>),
    InvariantError(EvalError, Vec<State>),
    AssumeViolation(usize),
    AssumeError(usize, EvalError),
    MaxStatesExceeded(CheckStats),
    MaxDepthExceeded(CheckStats),
    NoInitialStates,
    MissingConstants(Vec<Arc<str>>),
}

pub fn check(spec: &Spec, domains: &Env, config: &CheckerConfig) -> CheckResult {
    let user_constants = domains.clone();
    let mut domains = Env::new();
    stdlib::load_builtins(&mut domains);
    for module in &spec.extends {
        stdlib::load_module(module, &mut domains);
    }
    for (k, v) in user_constants {
        domains.insert(k, v);
    }

    #[cfg(not(target_arch = "wasm32"))]
    if !spec.instances.is_empty()
        && let Some(ref spec_path) = config.spec_path
    {
        let mut registry = ModuleRegistry::new();
        for inst in &spec.instances {
            match registry.load(&inst.module_name, spec_path) {
                Ok(_) => {}
                Err(e) => {
                    if !config.quiet {
                        eprintln!("  Warning: could not load module {}: {:?}", inst.module_name, e);
                    }
                }
            }
        }
        match resolve_instances(spec, &registry) {
            Ok(instances) => {
                if !instances.is_empty() && !config.quiet {
                    eprintln!("  Resolved {} instance(s)", instances.len());
                }
                set_resolved_instances(instances);
            }
            Err(e) => {
                if !config.quiet {
                    eprintln!("  Warning: could not resolve instances: {:?}", e);
                }
            }
        }
    }

    let missing: Vec<_> = spec
        .constants
        .iter()
        .filter(|c| !domains.contains_key(*c))
        .cloned()
        .collect();
    if !missing.is_empty() {
        return CheckResult::MissingConstants(missing);
    }

    for (idx, assume) in spec.assumes.iter().enumerate() {
        match eval(assume, &mut domains, &spec.definitions) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return CheckResult::AssumeViolation(idx),
            Ok(_) => {
                return CheckResult::AssumeError(
                    idx,
                    EvalError::TypeMismatch { expected: "Bool", got: Value::Bool(false), context: Some("ASSUME evaluation"),  span: None },
                )
            }
            Err(e) => return CheckResult::AssumeError(idx, e),
        }
    }

    let mut symmetry = SymmetryConfig::new();
    for sym_const in &config.symmetric_constants {
        if let Some(Value::Set(elements)) = domains.get(sym_const) {
            symmetry.add_symmetric_set(elements.clone());
        }
    }
    if !symmetry.is_empty() && !config.quiet {
        eprintln!(
            "  Symmetry reduction enabled for: {}",
            config.symmetric_constants.iter().map(|s| s.as_ref()).collect::<Vec<_>>().join(", ")
        );
    }

    update_checker_stats(EvalCheckerStats {
        distinct: 0,
        level: 0,
        diameter: 0,
        queue: 0,
        duration: 0,
        generated: 0,
    });

    if !config.quiet {
        eprintln!("  Computing initial states...");
    }
    let initial = match init_states(&spec.init, &spec.vars, &domains, &spec.definitions) {
        Ok(states) => states,
        Err(e) => return CheckResult::InitError(e),
    };
    if !config.quiet {
        eprintln!("  Found {} initial states", initial.len());
    }

    if initial.is_empty() {
        return CheckResult::NoInitialStates;
    }

    if !config.quiet {
        let limit_desc = if config.quick_mode {
            format!("{} states, quick mode", config.max_states)
        } else {
            format!("{} states", config.max_states)
        };
        eprintln!("  Starting exploration (limit: {})...", limit_desc);
    }

    #[cfg(not(target_arch = "wasm32"))]
    let start_time = Instant::now();
    #[cfg(not(target_arch = "wasm32"))]
    let elapsed_secs = || start_time.elapsed().as_secs_f64();
    #[cfg(target_arch = "wasm32")]
    let elapsed_secs = || 0.0_f64;
    #[cfg(not(target_arch = "wasm32"))]
    let elapsed_secs_i64 = || start_time.elapsed().as_secs() as i64;
    #[cfg(target_arch = "wasm32")]
    let elapsed_secs_i64 = || 0_i64;

    let mut states: IndexSet<State> = IndexSet::new();
    let mut parent: Vec<Option<usize>> = Vec::new();
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
    let mut stats = CheckStats {
        states_explored: 0,
        transitions: 0,
        max_depth_reached: 0,
        elapsed_secs: 0.0,
    };

    let base_env: Env = domains.clone();
    let primed_vars = make_primed_names(&spec.vars);
    let mut reusable_env = base_env.clone();

    for state in initial {
        let canonical = symmetry.canonicalize(&state).into_owned();
        let (idx, is_new) = states.insert_full(canonical);
        if is_new {
            parent.push(None);
            queue.push_back((idx, 1));
        }
    }

    let reconstruct_trace = |state_idx: usize, states: &IndexSet<State>, parent: &[Option<usize>]| -> Vec<State> {
        let mut trace = Vec::new();
        let mut idx = Some(state_idx);
        while let Some(i) = idx {
            trace.push(states.get_index(i).unwrap().clone());
            idx = parent[i];
        }
        trace.reverse();
        trace
    };

    #[cfg(not(target_arch = "wasm32"))]
    let do_export = |states: &IndexSet<State>, parent: &[Option<usize>], error_state: Option<usize>| {
        if let Some(ref path) = config.export_dot_path {
            match File::create(path) {
                Ok(file) => {
                    let mut writer = BufWriter::new(file);
                    if let Err(e) = export_dot(states, parent, &spec.vars, error_state, &mut writer) {
                        eprintln!("  Failed to write DOT export: {}", e);
                    } else {
                        eprintln!("  Exported state graph to {}", path.display());
                    }
                }
                Err(e) => eprintln!("  Failed to create DOT file: {}", e),
            }
        }
    };
    #[cfg(target_arch = "wasm32")]
    let do_export = |_states: &IndexSet<State>, _parent: &[Option<usize>], _error_state: Option<usize>| {};

    while let Some((current_idx, depth)) = queue.pop_front() {
        stats.states_explored += 1;
        stats.max_depth_reached = stats.max_depth_reached.max(depth);

        update_checker_stats(EvalCheckerStats {
            distinct: states.len() as i64,
            level: depth as i64,
            diameter: stats.max_depth_reached as i64,
            queue: queue.len() as i64,
            duration: elapsed_secs_i64(),
            generated: stats.transitions as i64,
        });

        let should_report = matches!(stats.states_explored, 1 | 10 | 100)
            || stats.states_explored.is_multiple_of(1000);
        if !config.quiet && should_report {
            if stats.states_explored == 1 {
                eprintln!("  Exploring states...");
            } else if stats.states_explored <= 100 {
                eprintln!(
                    "  Progress: {} states explored, queue: {}",
                    stats.states_explored, queue.len()
                );
            } else {
                let elapsed = elapsed_secs();
                let rate = stats.states_explored as f64 / elapsed.max(0.001);
                let remaining = config.max_states.saturating_sub(stats.states_explored);
                let eta = remaining as f64 / rate;
                let pct = (stats.states_explored as f64 / config.max_states as f64 * 100.0).min(100.0);
                let bar_width = 20;
                let filled = (pct / 100.0 * bar_width as f64) as usize;
                let empty = bar_width - filled;
                let bar: String = std::iter::repeat_n('\u{2588}', filled)
                    .chain(std::iter::repeat_n('\u{2591}', empty))
                    .collect();
                let eta_str = format_eta(eta);
                eprintln!(
                    "  [{}] {}/{} ({:.1}%) | {:.0}/s | depth: {} | ETA: {}",
                    bar, stats.states_explored, config.max_states, pct, rate, depth, eta_str
                );
            }
        }

        if stats.states_explored > config.max_states {
            stats.elapsed_secs = elapsed_secs();
            do_export(&states, &parent, None);
            return CheckResult::MaxStatesExceeded(stats);
        }

        if depth > config.max_depth {
            stats.elapsed_secs = elapsed_secs();
            do_export(&states, &parent, None);
            return CheckResult::MaxDepthExceeded(stats);
        }

        let current = states.get_index(current_idx).unwrap();
        let mut env = base_env.clone();
        for (i, var) in spec.vars.iter().enumerate() {
            if let Some(val) = current.values.get(i) {
                env.insert(var.clone(), val.clone());
            }
        }

        let ctx = EvalContext {
            state_vars: spec.vars.clone(),
            constants: domains.clone(),
            current_state: current.clone(),
        };

        for (idx, invariant) in spec.invariants.iter().enumerate() {
            match eval_with_context(invariant, &mut env, &spec.definitions, &ctx) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    let trace = reconstruct_trace(current_idx, &states, &parent);
                    stats.elapsed_secs = elapsed_secs();
                    do_export(&states, &parent, Some(current_idx));
                    return CheckResult::InvariantViolation(
                        Counterexample {
                            trace,
                            violated_invariant: idx,
                        },
                        stats,
                    );
                }
                Ok(_) => {
                    let trace = reconstruct_trace(current_idx, &states, &parent);
                    do_export(&states, &parent, Some(current_idx));
                    return CheckResult::InvariantError(
                        EvalError::TypeMismatch { expected: "Bool", got: Value::Bool(false), context: Some("invariant evaluation"),  span: None },
                        trace,
                    );
                }
                Err(e) => {
                    let trace = reconstruct_trace(current_idx, &states, &parent);
                    do_export(&states, &parent, Some(current_idx));
                    return CheckResult::InvariantError(e, trace);
                }
            }
        }

        let current = states.get_index(current_idx).unwrap();
        let successors = match next_states(&spec.next, current, &spec.vars, &primed_vars, &mut reusable_env, &spec.definitions) {
            Ok(s) => s,
            Err(e) => {
                let trace = reconstruct_trace(current_idx, &states, &parent);
                do_export(&states, &parent, Some(current_idx));
                return CheckResult::NextError(e, trace);
            }
        };
        if !config.quiet && stats.states_explored <= 5 {
            eprintln!("  State {} has {} successors", stats.states_explored, successors.len());
        }

        if successors.is_empty() && !config.allow_deadlock {
            let trace = reconstruct_trace(current_idx, &states, &parent);
            stats.elapsed_secs = elapsed_secs();
            do_export(&states, &parent, Some(current_idx));
            return CheckResult::Deadlock(trace, stats);
        }

        for successor in successors {
            stats.transitions += 1;
            let canonical = symmetry.canonicalize(&successor).into_owned();
            let (succ_idx, is_new) = states.insert_full(canonical);
            if is_new {
                parent.push(Some(current_idx));
                queue.push_back((succ_idx, depth + 1));
            }
        }
    }

    stats.elapsed_secs = elapsed_secs();
    do_export(&states, &parent, None);

    if config.check_liveness && (!spec.fairness.is_empty() || !spec.liveness_properties.is_empty()) {
        if !config.quiet {
            eprintln!("  Running liveness checking...");
        }
        match check_liveness_properties(spec, &states, &parent, &domains, &symmetry, config) {
            Ok(None) => {}
            Ok(Some(violation)) => {
                return CheckResult::LivenessViolation(violation, stats);
            }
            Err(e) => {
                return CheckResult::InvariantError(e, vec![]);
            }
        }
    }

    CheckResult::Ok(stats)
}

fn check_liveness_properties(
    spec: &Spec,
    states: &IndexSet<State>,
    parent: &[Option<usize>],
    domains: &Env,
    symmetry: &SymmetryConfig,
    config: &CheckerConfig,
) -> Result<Option<LivenessViolation>, EvalError> {
    let mut graph = StateGraph::new();

    for (idx, state) in states.iter().enumerate() {
        graph.add_state(state.clone(), parent[idx]);
    }

    if !config.quiet {
        eprintln!("  Building forward edges for {} states...", states.len());
    }
    let primed_vars = make_primed_names(&spec.vars);
    let mut reusable_env = domains.clone();
    for (state_idx, state) in states.iter().enumerate() {
        let successors = next_states(&spec.next, state, &spec.vars, &primed_vars, &mut reusable_env, &spec.definitions)?;
        for successor in successors {
            let canonical = symmetry.canonicalize(&successor);
            if let Some(succ_idx) = states.get_index_of(canonical.as_ref()) {
                graph.add_edge(state_idx, succ_idx, None);
            }
        }
    }

    if !config.quiet {
        eprintln!("  Computing strongly connected components...");
    }
    let sccs = compute_sccs(&graph);
    let nontrivial_count = sccs.iter().filter(|scc| !scc.is_trivial).count();
    if !config.quiet {
        eprintln!("  Found {} SCCs ({} non-trivial)", sccs.len(), nontrivial_count);
    }

    if !spec.fairness.is_empty() {
        let defs: Definitions = spec.definitions.clone();
        if let Some(scc_idx) = liveness::find_violating_scc(
            &graph,
            &sccs,
            &spec.fairness,
            &spec.vars,
            domains,
            &defs,
        )? {
            let violation = liveness::build_counterexample(
                &graph,
                &sccs[scc_idx],
                &spec.fairness,
                &spec.vars,
                domains,
                &defs,
            )?;
            return Ok(Some(violation));
        }
    }

    for property in &spec.liveness_properties {
        let defs: Definitions = spec.definitions.clone();
        for scc in &sccs {
            if !liveness::check_fairness_in_scc(&graph, scc, &spec.fairness, &spec.vars, domains, &defs)? {
                continue;
            }

            let property_satisfied = match property {
                Expr::LeadsTo(p, q) => {
                    liveness::check_leads_to(&graph, scc, p, q, domains, &defs, &spec.vars)?
                }
                _ => {
                    liveness::check_eventually(&graph, scc, property, domains, &defs, &spec.vars)?
                }
            };

            if !property_satisfied {
                let prop_desc = match property {
                    Expr::LeadsTo(_, _) => format!("{:?}", property),
                    _ => format!("<>{:?}", property),
                };
                let violation = LivenessViolation {
                    prefix: graph.reconstruct_trace(scc.states[0]),
                    cycle: scc.states.iter().filter_map(|&idx| graph.get_state(idx).cloned()).collect(),
                    property: prop_desc,
                    fairness_info: vec![],
                };
                return Ok(Some(violation));
            }
        }
    }

    Ok(None)
}

pub fn format_trace(trace: &[State], vars: &[Arc<str>]) -> String {
    let mut out = String::new();
    for (i, state) in trace.iter().enumerate() {
        out.push_str(&format!("State {}\n", i));
        for (vi, var) in vars.iter().enumerate() {
            if let Some(val) = state.values.get(vi) {
                out.push_str(&format!("  {} = {}\n", var, format_value(val)));
            }
        }
    }
    out
}

pub fn format_trace_with_diffs(trace: &[State], vars: &[Arc<str>]) -> String {
    if trace.is_empty() {
        return String::new();
    }

    let max_var_len = vars.iter().map(|v| v.len()).max().unwrap_or(0);
    let total_states = trace.len();
    let last_idx = total_states - 1;

    let mut out = String::new();
    for (i, state) in trace.iter().enumerate() {
        let prev = if i > 0 { Some(&trace[i - 1]) } else { None };

        let changed_vars: Vec<&str> = vars
            .iter()
            .enumerate()
            .filter(|(vi, _)| {
                if let (Some(p), Some(curr)) = (prev.and_then(|p| p.values.get(*vi)), state.values.get(*vi)) {
                    p != curr
                } else {
                    false
                }
            })
            .map(|(_, s)| s.as_ref())
            .collect();

        if i == last_idx && total_states > 1 {
            out.push_str(&format!("State {} of {} [FINAL]\n", i, last_idx));
        } else if total_states > 1 {
            out.push_str(&format!("State {} of {}\n", i, last_idx));
        } else {
            out.push_str(&format!("State {}\n", i));
        }

        if !changed_vars.is_empty() && i > 0 {
            out.push_str(&format!("  (changed: {})\n", changed_vars.join(", ")));
        }

        for (vi, var) in vars.iter().enumerate() {
            if let Some(val) = state.values.get(vi) {
                let changed = prev.is_some_and(|p| p.values.get(vi) != Some(val));
                let marker = if changed { " *" } else { "" };
                let prev_val_str = if changed {
                    prev.and_then(|p| p.values.get(vi))
                        .map(|v| format!("  (was: {})", format_value(v)))
                        .unwrap_or_default()
                } else {
                    String::new()
                };
                out.push_str(&format!(
                    "  {:width$} = {}{}{}\n",
                    var,
                    format_value(val),
                    prev_val_str,
                    marker,
                    width = max_var_len
                ));
            }
        }
    }
    out
}

pub fn format_value(val: &Value) -> String {
    match val {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Set(s) => {
            let elems: Vec<_> = s.iter().map(format_value).collect();
            format!("{{{}}}", elems.join(", "))
        }
        Value::Fn(f) => {
            let pairs: Vec<_> = f
                .iter()
                .map(|(k, v)| format!("{} :> {}", format_value(k), format_value(v)))
                .collect();
            format!("({})", pairs.join(" @@ "))
        }
        Value::Record(r) => {
            let fields: Vec<_> = r
                .iter()
                .map(|(k, v)| format!("{} |-> {}", k, format_value(v)))
                .collect();
            format!("[{}]", fields.join(", "))
        }
        Value::Tuple(t) => {
            let elems: Vec<_> = t.iter().map(format_value).collect();
            format!("<<{}>>", elems.join(", "))
        }
    }
}

pub fn format_eval_error(err: &EvalError) -> String {
    match err {
        EvalError::UndefinedVar { name, suggestion, .. } => {
            let mut msg = format!("undefined variable `{}`", name);
            if let Some(s) = suggestion {
                msg.push_str(&format!("\n  help: did you mean `{}`?", s));
            }
            msg
        }
        EvalError::TypeMismatch { expected, got, context, .. } => {
            let type_name = value_type_name(got);
            let mut msg = format!("type mismatch: expected {}, got {}", expected, type_name);
            if let Some(ctx) = context {
                msg.push_str(&format!(" (in {})", ctx));
            }
            msg
        }
        EvalError::DivisionByZero { .. } => "division by zero".to_string(),
        EvalError::EmptyChoose { .. } => {
            "CHOOSE found no satisfying value (domain may be empty or no element satisfies the predicate)".to_string()
        }
        EvalError::DomainError { message, .. } => message.clone(),
    }
}

fn value_type_name(val: &Value) -> &'static str {
    match val {
        Value::Bool(_) => "Bool",
        Value::Int(_) => "Int",
        Value::Str(_) => "Str",
        Value::Set(_) => "Set",
        Value::Fn(_) => "Function",
        Value::Record(_) => "Record",
        Value::Tuple(_) => "Sequence",
    }
}

pub fn eval_error_to_diagnostic(err: &EvalError) -> crate::diagnostic::Diagnostic {
    use crate::diagnostic::Diagnostic;
    let diag = match err {
        EvalError::UndefinedVar { name, suggestion, .. } => {
            let mut diag = Diagnostic::error(format!("undefined variable `{}`", name));
            if let Some(s) = suggestion {
                diag = diag.with_help(format!("did you mean `{}`?", s));
            }
            diag
        }
        EvalError::TypeMismatch { expected, got, context, .. } => {
            let type_name = value_type_name(got);
            let msg = if let Some(ctx) = context {
                format!("type mismatch in {}: expected {}, got {}", ctx, expected, type_name)
            } else {
                format!("type mismatch: expected {}, got {}", expected, type_name)
            };
            Diagnostic::error(msg)
        }
        EvalError::DivisionByZero { .. } => Diagnostic::error("division by zero"),
        EvalError::EmptyChoose { .. } => {
            Diagnostic::error("CHOOSE found no satisfying value")
                .with_help("the domain may be empty or no element satisfies the predicate")
        }
        EvalError::DomainError { message, .. } => Diagnostic::error(message.clone()),
    };
    if let Some(span) = err.span() {
        diag.with_span(span)
    } else {
        diag
    }
}

pub fn value_to_json(val: &Value) -> String {
    match val {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Str(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
        Value::Set(s) => {
            let elems: Vec<_> = s.iter().map(value_to_json).collect();
            format!("[{}]", elems.join(", "))
        }
        Value::Fn(f) => {
            let pairs: Vec<_> = f
                .iter()
                .map(|(k, v)| format!("{{\"key\": {}, \"value\": {}}}", value_to_json(k), value_to_json(v)))
                .collect();
            format!("[{}]", pairs.join(", "))
        }
        Value::Record(r) => {
            let fields: Vec<_> = r
                .iter()
                .map(|(k, v)| format!("\"{}\": {}", k, value_to_json(v)))
                .collect();
            format!("{{{}}}", fields.join(", "))
        }
        Value::Tuple(t) => {
            let elems: Vec<_> = t.iter().map(value_to_json).collect();
            format!("[{}]", elems.join(", "))
        }
    }
}

pub fn state_to_json(state: &State, vars: &[Arc<str>]) -> String {
    let fields: Vec<_> = vars
        .iter()
        .enumerate()
        .filter_map(|(i, var)| {
            state.values.get(i).map(|val| format!("\"{}\": {}", var, value_to_json(val)))
        })
        .collect();
    format!("{{{}}}", fields.join(", "))
}

pub fn trace_to_json(trace: &[State], vars: &[Arc<str>]) -> String {
    let states: Vec<_> = trace
        .iter()
        .enumerate()
        .map(|(i, state)| format!("{{\"index\": {}, \"state\": {}}}", i, state_to_json(state, vars)))
        .collect();
    format!("[{}]", states.join(", "))
}

pub fn check_result_to_json(result: &CheckResult, spec: &Spec) -> String {
    match result {
        CheckResult::Ok(stats) => {
            format!(
                r#"{{"status": "ok", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored, stats.transitions, stats.max_depth_reached, stats.elapsed_secs
            )
        }
        CheckResult::InvariantViolation(cex, stats) => {
            let inv_name = spec
                .invariant_names
                .get(cex.violated_invariant)
                .and_then(|n| n.as_ref())
                .map(|n| format!("\"{}\"", n))
                .unwrap_or_else(|| "null".to_string());
            format!(
                r#"{{"status": "invariant_violation", "invariant_index": {}, "invariant_name": {}, "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                cex.violated_invariant,
                inv_name,
                trace_to_json(&cex.trace, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::Deadlock(trace, stats) => {
            format!(
                r#"{{"status": "deadlock", "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                trace_to_json(trace, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::InitError(e) => {
            format!(r#"{{"status": "init_error", "error": "{}"}}"#, format_eval_error(e).replace('"', "\\\""))
        }
        CheckResult::NextError(e, trace) => {
            format!(
                r#"{{"status": "next_error", "error": "{}", "trace": {}}}"#,
                format_eval_error(e).replace('"', "\\\""),
                trace_to_json(trace, &spec.vars)
            )
        }
        CheckResult::InvariantError(e, trace) => {
            format!(
                r#"{{"status": "invariant_error", "error": "{}", "trace": {}}}"#,
                format_eval_error(e).replace('"', "\\\""),
                trace_to_json(trace, &spec.vars)
            )
        }
        CheckResult::MaxStatesExceeded(stats) => {
            format!(
                r#"{{"status": "max_states_exceeded", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored, stats.transitions, stats.max_depth_reached, stats.elapsed_secs
            )
        }
        CheckResult::MaxDepthExceeded(stats) => {
            format!(
                r#"{{"status": "max_depth_exceeded", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored, stats.transitions, stats.max_depth_reached, stats.elapsed_secs
            )
        }
        CheckResult::NoInitialStates => {
            r#"{"status": "no_initial_states"}"#.to_string()
        }
        CheckResult::MissingConstants(missing) => {
            let names: Vec<_> = missing.iter().map(|c| format!("\"{}\"", c)).collect();
            format!(r#"{{"status": "missing_constants", "constants": [{}]}}"#, names.join(", "))
        }
        CheckResult::AssumeViolation(idx) => {
            format!(r#"{{"status": "assume_violation", "assume_index": {}}}"#, idx)
        }
        CheckResult::AssumeError(idx, e) => {
            format!(
                r#"{{"status": "assume_error", "assume_index": {}, "error": "{}"}}"#,
                idx,
                format_eval_error(e).replace('"', "\\\"")
            )
        }
        CheckResult::LivenessViolation(violation, stats) => {
            format!(
                r#"{{"status": "liveness_violation", "property": "{}", "prefix": {}, "cycle": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                violation.property.replace('"', "\\\""),
                trace_to_json(&violation.prefix, &spec.vars),
                trace_to_json(&violation.cycle, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub fn write_trace_json(path: &std::path::Path, trace: &[State], vars: &[Arc<str>]) -> std::io::Result<()> {
    use std::io::Write;
    let mut file = std::fs::File::create(path)?;
    writeln!(file, "{}", trace_to_json(trace, vars))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::ast::Expr;

    fn var(name: &str) -> Arc<str> {
        Arc::from(name)
    }

    fn lit_int(n: i64) -> Expr {
        Expr::Lit(Value::Int(n))
    }

    fn lit_bool(b: bool) -> Expr {
        Expr::Lit(Value::Bool(b))
    }

    fn var_expr(name: &str) -> Expr {
        Expr::Var(var(name))
    }

    fn prime_expr(name: &str) -> Expr {
        Expr::Prime(var(name))
    }

    fn eq(l: Expr, r: Expr) -> Expr {
        Expr::Eq(Box::new(l), Box::new(r))
    }

    fn and(l: Expr, r: Expr) -> Expr {
        Expr::And(Box::new(l), Box::new(r))
    }

    fn or(l: Expr, r: Expr) -> Expr {
        Expr::Or(Box::new(l), Box::new(r))
    }

    fn le(l: Expr, r: Expr) -> Expr {
        Expr::Le(Box::new(l), Box::new(r))
    }

    fn lt(l: Expr, r: Expr) -> Expr {
        Expr::Lt(Box::new(l), Box::new(r))
    }

    fn add(l: Expr, r: Expr) -> Expr {
        Expr::Add(Box::new(l), Box::new(r))
    }

    fn in_set(elem: Expr, set: Expr) -> Expr {
        Expr::In(Box::new(elem), Box::new(set))
    }

    fn set_range(lo: Expr, hi: Expr) -> Expr {
        Expr::SetRange(Box::new(lo), Box::new(hi))
    }

    #[test]
    fn counter_passes() {
        let spec = Spec {
            vars: vec![var("count")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: eq(var_expr("count"), lit_int(0)),
            next: and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            ),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig {
            allow_deadlock: true,
            ..CheckerConfig::default()
        };
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::Ok(stats) => {
                assert_eq!(stats.states_explored, 4);
                assert_eq!(stats.transitions, 3);
            }
            other => panic!("expected Ok, got {:?}", other),
        }
    }

    #[test]
    fn counter_fails_invariant() {
        let spec = Spec {
            vars: vec![var("count")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: eq(var_expr("count"), lit_int(0)),
            next: and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(4))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            ),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig::default();
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::InvariantViolation(cex, _stats) => {
                assert_eq!(cex.violated_invariant, 0);
                assert_eq!(cex.trace.len(), 5);
                let final_state = cex.trace.last().unwrap();
                assert_eq!(final_state.values.get(0), Some(&Value::Int(4)));
            }
            other => panic!("expected InvariantViolation, got {:?}", other),
        }
    }

    #[test]
    fn two_bit_counter() {
        let spec = Spec {
            vars: vec![var("lo"), var("hi")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: and(
                eq(var_expr("lo"), lit_int(0)),
                eq(var_expr("hi"), lit_int(0)),
            ),
            next: or(
                and(
                    lt(var_expr("lo"), lit_int(1)),
                    and(
                        eq(prime_expr("lo"), add(var_expr("lo"), lit_int(1))),
                        eq(prime_expr("hi"), var_expr("hi")),
                    ),
                ),
                and(
                    eq(var_expr("lo"), lit_int(1)),
                    and(
                        eq(prime_expr("lo"), lit_int(0)),
                        eq(prime_expr("hi"), add(var_expr("hi"), lit_int(1))),
                    ),
                ),
            ),
            invariants: vec![
                le(var_expr("lo"), lit_int(1)),
                le(var_expr("hi"), lit_int(1)),
            ],
            invariant_names: vec![None, None],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig::default();
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::InvariantViolation(cex, _stats) => {
                assert_eq!(cex.violated_invariant, 1);
                let final_state = cex.trace.last().unwrap();
                assert_eq!(final_state.values.get(1), Some(&Value::Int(2)));
            }
            other => panic!("expected InvariantViolation, got {:?}", other),
        }
    }

    #[test]
    fn deadlock_spec_allowed() {
        let spec = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: eq(var_expr("x"), lit_int(0)),
            next: and(
                eq(var_expr("x"), lit_int(99)),
                eq(prime_expr("x"), lit_int(100)),
            ),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig {
            allow_deadlock: true,
            ..CheckerConfig::default()
        };
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::Ok(stats) => {
                assert_eq!(stats.states_explored, 1);
                assert_eq!(stats.transitions, 0);
            }
            other => panic!("expected Ok (deadlock allowed), got {:?}", other),
        }
    }

    #[test]
    fn deadlock_detected() {
        let spec = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: eq(var_expr("x"), lit_int(0)),
            next: and(
                lt(var_expr("x"), lit_int(2)),
                eq(prime_expr("x"), add(var_expr("x"), lit_int(1))),
            ),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
            fairness: vec![],
            liveness_properties: vec![],
        };

        let result = check(&spec, &Env::new(), &CheckerConfig::default());
        match result {
            CheckResult::Deadlock(trace, _) => {
                assert_eq!(trace.len(), 3);
                let final_state = trace.last().unwrap();
                assert_eq!(final_state.values.get(0), Some(&Value::Int(2)));
            }
            other => panic!("expected Deadlock, got {:?}", other),
        }
    }

    #[test]
    fn format_trace_output() {
        let state = State {
            values: vec![Value::Int(42), Value::Set([Value::Int(1), Value::Int(2)].into())],
        };

        let trace = vec![state];
        let vars = vec![var("x"), var("y")];
        let output = format_trace(&trace, &vars);

        assert!(output.contains("State 0"));
        assert!(output.contains("x = 42"));
        assert!(output.contains("y = {1, 2}"));
    }
}
