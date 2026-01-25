use std::collections::VecDeque;
use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use indexmap::IndexSet;

use crate::ast::{Env, Spec, State, Value};
use crate::eval::{eval, init_states, next_states, update_checker_stats, CheckerStats as EvalCheckerStats, EvalError};
use crate::export::export_dot;
use crate::stdlib;
use crate::symmetry::SymmetryConfig;

#[derive(Debug)]
pub struct CheckerConfig {
    pub max_states: usize,
    pub max_depth: usize,
    pub symmetric_constants: Vec<Arc<str>>,
    pub export_dot_path: Option<PathBuf>,
    pub allow_deadlock: bool,
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            max_states: 1_000_000,
            max_depth: 100,
            symmetric_constants: Vec::new(),
            export_dot_path: None,
            allow_deadlock: false,
        }
    }
}

impl CheckerConfig {
    pub fn new() -> Self {
        Self::default()
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
        match eval(assume, &domains, &spec.definitions) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return CheckResult::AssumeViolation(idx),
            Ok(_) => {
                return CheckResult::AssumeError(
                    idx,
                    EvalError::TypeMismatch {
                        expected: "Bool",
                        got: Value::Bool(false),
                    },
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
    if !symmetry.is_empty() {
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

    eprintln!("  Computing initial states...");
    let initial = match init_states(&spec.init, &spec.vars, &domains, &spec.definitions) {
        Ok(states) => states,
        Err(e) => return CheckResult::InitError(e),
    };
    eprintln!("  Found {} initial states", initial.len());

    if initial.is_empty() {
        return CheckResult::NoInitialStates;
    }

    let start_time = Instant::now();
    let mut states: IndexSet<State> = IndexSet::new();
    let mut parent: Vec<Option<usize>> = Vec::new();
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
    let mut stats = CheckStats {
        states_explored: 0,
        transitions: 0,
        max_depth_reached: 0,
        elapsed_secs: 0.0,
    };

    for state in initial {
        let canonical = symmetry.canonicalize(&state);
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

    while let Some((current_idx, depth)) = queue.pop_front() {
        stats.states_explored += 1;
        stats.max_depth_reached = stats.max_depth_reached.max(depth);

        update_checker_stats(EvalCheckerStats {
            distinct: states.len() as i64,
            level: depth as i64,
            diameter: stats.max_depth_reached as i64,
            queue: queue.len() as i64,
            duration: start_time.elapsed().as_secs() as i64,
            generated: stats.transitions as i64,
        });

        if stats.states_explored.is_multiple_of(1000) {
            let elapsed = start_time.elapsed().as_secs_f64();
            let rate = stats.states_explored as f64 / elapsed.max(0.001);
            let remaining = config.max_states.saturating_sub(stats.states_explored);
            let eta = remaining as f64 / rate;
            eprintln!(
                "  Progress: {} states ({:.0}/s), queue: {}, depth: {}, limit ETA: {:.1}s",
                stats.states_explored, rate, queue.len(), depth, eta
            );
        }

        if stats.states_explored > config.max_states {
            stats.elapsed_secs = start_time.elapsed().as_secs_f64();
            do_export(&states, &parent, None);
            return CheckResult::MaxStatesExceeded(stats);
        }

        if depth > config.max_depth {
            stats.elapsed_secs = start_time.elapsed().as_secs_f64();
            do_export(&states, &parent, None);
            return CheckResult::MaxDepthExceeded(stats);
        }

        let current = states.get_index(current_idx).unwrap();
        let mut env = state_to_env(current);
        for (k, v) in &domains {
            env.insert(k.clone(), v.clone());
        }

        for (idx, invariant) in spec.invariants.iter().enumerate() {
            match eval(invariant, &env, &spec.definitions) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    let trace = reconstruct_trace(current_idx, &states, &parent);
                    stats.elapsed_secs = start_time.elapsed().as_secs_f64();
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
                        EvalError::TypeMismatch {
                            expected: "Bool",
                            got: Value::Bool(false),
                        },
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
        let successors = match next_states(&spec.next, current, &spec.vars, &domains, &spec.definitions) {
            Ok(s) => s,
            Err(e) => {
                let trace = reconstruct_trace(current_idx, &states, &parent);
                do_export(&states, &parent, Some(current_idx));
                return CheckResult::NextError(e, trace);
            }
        };
        if stats.states_explored <= 5 {
            eprintln!("  State {} has {} successors", stats.states_explored, successors.len());
        }

        if successors.is_empty() && !config.allow_deadlock {
            let trace = reconstruct_trace(current_idx, &states, &parent);
            stats.elapsed_secs = start_time.elapsed().as_secs_f64();
            do_export(&states, &parent, Some(current_idx));
            return CheckResult::Deadlock(trace, stats);
        }

        for successor in successors {
            stats.transitions += 1;
            let canonical = symmetry.canonicalize(&successor);
            let (succ_idx, is_new) = states.insert_full(canonical);
            if is_new {
                parent.push(Some(current_idx));
                queue.push_back((succ_idx, depth + 1));
            }
        }
    }

    stats.elapsed_secs = start_time.elapsed().as_secs_f64();
    do_export(&states, &parent, None);
    CheckResult::Ok(stats)
}

fn state_to_env(state: &State) -> Env {
    state.vars.clone()
}

pub fn format_trace(trace: &[State], vars: &[Arc<str>]) -> String {
    let mut out = String::new();
    for (i, state) in trace.iter().enumerate() {
        out.push_str(&format!("State {}\n", i));
        for var in vars {
            if let Some(val) = state.vars.get(var) {
                out.push_str(&format!("  {} = {}\n", var, format_value(val)));
            }
        }
    }
    out
}

pub fn format_trace_with_diffs(trace: &[State], vars: &[Arc<str>]) -> String {
    let mut out = String::new();
    for (i, state) in trace.iter().enumerate() {
        out.push_str(&format!("State {}\n", i));
        let prev = if i > 0 { Some(&trace[i - 1]) } else { None };
        for var in vars {
            if let Some(val) = state.vars.get(var) {
                let changed = prev.is_some_and(|p| p.vars.get(var) != Some(val));
                let marker = if changed { " *" } else { "" };
                out.push_str(&format!("  {} = {}{}\n", var, format_value(val), marker));
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
            init: eq(var_expr("count"), lit_int(0)),
            next: and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            ),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
        };

        let domains = Env::new();
        let mut config = CheckerConfig::default();
        config.allow_deadlock = true;
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
            init: eq(var_expr("count"), lit_int(0)),
            next: and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(4))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            ),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
        };

        let domains = Env::new();
        let config = CheckerConfig::default();
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::InvariantViolation(cex, _stats) => {
                assert_eq!(cex.violated_invariant, 0);
                assert_eq!(cex.trace.len(), 5);
                let final_state = cex.trace.last().unwrap();
                assert_eq!(final_state.vars.get(&var("count")), Some(&Value::Int(4)));
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
        };

        let domains = Env::new();
        let config = CheckerConfig::default();
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::InvariantViolation(cex, _stats) => {
                assert_eq!(cex.violated_invariant, 1);
                let final_state = cex.trace.last().unwrap();
                assert_eq!(final_state.vars.get(&var("hi")), Some(&Value::Int(2)));
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
            init: eq(var_expr("x"), lit_int(0)),
            next: and(
                eq(var_expr("x"), lit_int(99)),
                eq(prime_expr("x"), lit_int(100)),
            ),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
        };

        let domains = Env::new();
        let mut config = CheckerConfig::default();
        config.allow_deadlock = true;
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
            init: eq(var_expr("x"), lit_int(0)),
            next: and(
                lt(var_expr("x"), lit_int(2)),
                eq(prime_expr("x"), add(var_expr("x"), lit_int(1))),
            ),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
        };

        let result = check(&spec, &Env::new(), &CheckerConfig::default());
        match result {
            CheckResult::Deadlock(trace, _) => {
                assert_eq!(trace.len(), 3);
                let final_state = trace.last().unwrap();
                assert_eq!(final_state.vars.get(&var("x")), Some(&Value::Int(2)));
            }
            other => panic!("expected Deadlock, got {:?}", other),
        }
    }

    #[test]
    fn format_trace_output() {
        let mut state = State::new();
        state.vars.insert(var("x"), Value::Int(42));
        state.vars.insert(var("y"), Value::Set([Value::Int(1), Value::Int(2)].into()));

        let trace = vec![state];
        let vars = vec![var("x"), var("y")];
        let output = format_trace(&trace, &vars);

        assert!(output.contains("State 0"));
        assert!(output.contains("x = 42"));
        assert!(output.contains("y = {1, 2}"));
    }
}
