use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Arc;

use super::{ParameterizedInstances, ResolvedInstances};
use crate::ast::{Env, State, Value};

#[derive(Clone)]
pub struct EvalContext {
    pub state_vars: Vec<Arc<str>>,
    pub constants: Env,
    pub current_state: State,
}

#[cfg(feature = "profiling")]
#[derive(Debug, Clone, Default)]
pub struct ProfilingStats {
    pub eval_calls: u64,
    pub next_states_time_ns: u128,
    pub next_states_calls: u64,
    pub enumerate_next_time_ns: u128,
    pub enumerate_next_calls: u64,
    pub infer_candidates_time_ns: u128,
    pub infer_candidates_calls: u64,
    pub init_states_time_ns: u128,
    pub init_states_calls: u64,
}

#[cfg(feature = "profiling")]
impl ProfilingStats {
    pub const fn new() -> Self {
        Self {
            eval_calls: 0,
            next_states_time_ns: 0,
            next_states_calls: 0,
            enumerate_next_time_ns: 0,
            enumerate_next_calls: 0,
            infer_candidates_time_ns: 0,
            infer_candidates_calls: 0,
            init_states_time_ns: 0,
            init_states_calls: 0,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CheckerStats {
    pub distinct: i64,
    pub level: i64,
    pub diameter: i64,
    pub queue: i64,
    pub duration: i64,
    pub generated: i64,
}

impl CheckerStats {
    pub const fn new() -> Self {
        Self {
            distinct: 0,
            level: 0,
            diameter: 0,
            queue: 0,
            duration: 0,
            generated: 0,
        }
    }
}

thread_local! {
    pub(super) static RNG: RefCell<fastrand::Rng> = RefCell::new(fastrand::Rng::with_seed(0));
    pub(super) static TLC_STATE: RefCell<BTreeMap<i64, Value>> = const { RefCell::new(BTreeMap::new()) };
    pub(super) static CHECKER_STATS: RefCell<CheckerStats> = const { RefCell::new(CheckerStats::new()) };
    pub(super) static RESOLVED_INSTANCES: RefCell<ResolvedInstances> = const { RefCell::new(BTreeMap::new()) };
    pub(super) static PARAMETERIZED_INSTANCES: RefCell<ParameterizedInstances> = const { RefCell::new(BTreeMap::new()) };
    #[cfg(feature = "profiling")]
    pub(super) static PROFILING_STATS: RefCell<ProfilingStats> = const { RefCell::new(ProfilingStats::new()) };
}

pub fn set_random_seed(seed: u64) {
    RNG.with(|rng| *rng.borrow_mut() = fastrand::Rng::with_seed(seed));
}

pub fn reset_tlc_state() {
    TLC_STATE.with(|state| state.borrow_mut().clear());
}

pub fn update_checker_stats(stats: CheckerStats) {
    CHECKER_STATS.with(|s| *s.borrow_mut() = stats);
}

pub fn set_checker_level(level: i64) {
    CHECKER_STATS.with(|s| s.borrow_mut().level = level);
}

pub fn set_resolved_instances(instances: ResolvedInstances) {
    RESOLVED_INSTANCES.with(|inst| *inst.borrow_mut() = instances);
}

pub fn clear_resolved_instances() {
    RESOLVED_INSTANCES.with(|inst| inst.borrow_mut().clear());
    PARAMETERIZED_INSTANCES.with(|inst| inst.borrow_mut().clear());
}

pub fn set_parameterized_instances(instances: ParameterizedInstances) {
    PARAMETERIZED_INSTANCES.with(|inst| *inst.borrow_mut() = instances);
}

#[cfg(feature = "profiling")]
pub fn reset_profiling_stats() {
    PROFILING_STATS.with(|s| *s.borrow_mut() = ProfilingStats::new());
}

#[cfg(feature = "profiling")]
pub fn get_profiling_stats() -> ProfilingStats {
    PROFILING_STATS.with(|s| s.borrow().clone())
}

#[cfg(feature = "profiling")]
pub fn report_profiling_stats() {
    let stats = get_profiling_stats();
    let next_states_ms = stats.next_states_time_ns / 1_000_000;
    let enumerate_ms = stats.enumerate_next_time_ns / 1_000_000;
    let infer_ms = stats.infer_candidates_time_ns / 1_000_000;
    let init_ms = stats.init_states_time_ns / 1_000_000;

    eprintln!("=== Profiling Stats ===");
    eprintln!("eval:             {:>12} calls", stats.eval_calls);
    eprintln!(
        "init_states:      {:>8}ms ({} calls, {:.2}µs/call)",
        init_ms,
        stats.init_states_calls,
        if stats.init_states_calls > 0 {
            stats.init_states_time_ns as f64 / stats.init_states_calls as f64 / 1000.0
        } else {
            0.0
        }
    );
    eprintln!(
        "next_states:      {:>8}ms ({} calls, {:.2}µs/call)",
        next_states_ms,
        stats.next_states_calls,
        if stats.next_states_calls > 0 {
            stats.next_states_time_ns as f64 / stats.next_states_calls as f64 / 1000.0
        } else {
            0.0
        }
    );
    eprintln!(
        "enumerate_next:   {:>8}ms ({} calls, {:.2}µs/call)",
        enumerate_ms,
        stats.enumerate_next_calls,
        if stats.enumerate_next_calls > 0 {
            stats.enumerate_next_time_ns as f64 / stats.enumerate_next_calls as f64 / 1000.0
        } else {
            0.0
        }
    );
    eprintln!(
        "infer_candidates: {:>8}ms ({} calls, {:.2}µs/call)",
        infer_ms,
        stats.infer_candidates_calls,
        if stats.infer_candidates_calls > 0 {
            stats.infer_candidates_time_ns as f64 / stats.infer_candidates_calls as f64 / 1000.0
        } else {
            0.0
        }
    );
    eprintln!("=======================");
}
