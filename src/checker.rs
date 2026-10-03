use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
#[cfg(not(target_arch = "wasm32"))]
use std::fs::File;
#[cfg(not(target_arch = "wasm32"))]
use std::io::BufWriter;
use std::path::PathBuf;
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use indexmap::IndexSet;

use crate::ast::{Env, Expr, SafetyProperty, Spec, State, Value};
use crate::eval::{
    CheckerStats as EvalCheckerStats, Definitions, EvalContext, EvalError, contains_prime_ref,
    eval, eval_with_context, expr_contains, expr_references, init_states, make_primed_names,
    next_states, update_checker_stats,
};
#[cfg(not(target_arch = "wasm32"))]
use crate::eval::{set_parameterized_instances, set_resolved_instances};
use crate::export::{DotExport, DotMode, EdgeList, export_dot};
use crate::graph::StateGraph;
use crate::liveness::{self, LivenessViolation};
#[cfg(not(target_arch = "wasm32"))]
use crate::modules::{ModuleError, ModuleRegistry, resolve_instances};
use crate::stdlib;
use crate::symmetry::SymmetryConfig;

#[derive(Debug)]
pub struct CheckerConfig {
    pub max_states: usize,
    pub max_depth: usize,
    pub max_seconds: Option<u64>,
    pub symmetric_constants: Vec<Arc<str>>,
    #[cfg(not(target_arch = "wasm32"))]
    pub export_dot_path: Option<PathBuf>,
    pub allow_deadlock: bool,
    pub check_liveness: bool,
    pub quiet: bool,
    pub quick_mode: bool,
    pub verbosity: u8,
    pub json_output: bool,
    pub continue_on_violation: bool,
    pub count_properties: Vec<Arc<str>>,
    pub export_dot_string: bool,
    pub dot_mode: DotMode,
    pub spec_path: Option<PathBuf>,
    #[cfg(not(target_arch = "wasm32"))]
    pub trace_json_path: Option<PathBuf>,
    pub state_constraints: Vec<Expr>,
    pub allow_unassigned_stutter: bool,
    pub use_inference_engine: bool,
    /// Treat `Nat` and `Int` as symbolic infinite sets (membership works,
    /// enumeration errors) instead of the bounded finite approximation.
    pub symbolic_integers: bool,
    /// Maximum enumerable sizes for the eager set-enumeration operators
    /// (`SUBSET`, `Permutations`, `SubBag`); raising them trades safety against
    /// state/space blowup.
    pub max_powerset: usize,
    pub max_permutations: usize,
    pub max_subbag_copies: usize,
    /// Verify that the concrete spec refines the abstract spec reached through the
    /// named non-parameterized `INSTANCE` alias — `Spec => Alias!Spec`. Each
    /// concrete transition must satisfy the abstract `Next` or leave the abstract
    /// state unchanged (a stutter), and every initial state must satisfy the
    /// abstract `Init`.
    pub check_refinement: Option<Arc<str>>,
    /// Names of the cfg `PROPERTY` definitions, reported as checked on success.
    pub properties: Vec<Arc<str>>,
    /// Which liveness checker runs: the property-shape checks, or the tableau of
    /// the negated property (any temporal formula, with TLC's classification).
    pub liveness_engine: LivenessEngine,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum LivenessEngine {
    Legacy,
    #[default]
    Tableau,
}

impl LivenessEngine {
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "legacy" => Some(Self::Legacy),
            "tableau" => Some(Self::Tableau),
            _ => None,
        }
    }
}

impl Default for CheckerConfig {
    fn default() -> Self {
        Self {
            max_states: 1_000_000,
            max_depth: 100,
            max_seconds: None,
            symmetric_constants: Vec::new(),
            #[cfg(not(target_arch = "wasm32"))]
            export_dot_path: None,
            allow_deadlock: false,
            check_liveness: false,
            quiet: false,
            quick_mode: false,
            verbosity: 1,
            json_output: false,
            continue_on_violation: false,
            count_properties: Vec::new(),
            export_dot_string: false,
            dot_mode: DotMode::default(),
            spec_path: None,
            #[cfg(not(target_arch = "wasm32"))]
            trace_json_path: None,
            state_constraints: Vec::new(),
            allow_unassigned_stutter: false,
            use_inference_engine: false,
            symbolic_integers: false,
            max_powerset: 20,
            max_permutations: 10,
            max_subbag_copies: 20,
            check_refinement: None,
            properties: Vec::new(),
            liveness_engine: LivenessEngine::default(),
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
    pub actions: Vec<Option<Arc<str>>>,
    pub violated_invariant: usize,
}

/// A concrete behavior that breaks the refinement `Spec => Alias!Spec`: either an
/// initial state whose abstract image fails the abstract `Init`, or a transition
/// whose abstract image is neither an abstract `Next` step nor a stutter.
#[derive(Debug)]
pub struct RefinementViolation {
    pub trace: Vec<State>,
    pub actions: Vec<Option<Arc<str>>>,
    pub alias: Arc<str>,
    pub at_init: bool,
}

/// Which safety part of a cfg `PROPERTY` failed: a state predicate on an initial
/// state, or a `[][A]_v` conjunct on a transition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyViolationKind {
    Init,
    Action,
}

/// A behavior that violates the safety part of a cfg `PROPERTY`. For `Init` the trace
/// is the offending initial state; for `Action` it ends with the offending transition.
#[derive(Debug)]
pub struct PropertyViolation {
    pub property: Arc<str>,
    pub kind: PropertyViolationKind,
    pub trace: Vec<State>,
    pub actions: Vec<Option<Arc<str>>>,
}

#[derive(Debug)]
pub struct CheckStats {
    pub states_explored: usize,
    pub transitions: usize,
    pub transitions_by_action: BTreeMap<Option<Arc<str>>, usize>,
    pub max_depth_reached: usize,
    pub elapsed_secs: f64,
    pub violation_count: usize,
    pub violation_traces: Vec<Counterexample>,
    pub violations_by_invariant: Vec<(Option<Arc<str>>, usize)>,
    pub property_stats: Vec<PropertyStats>,
    pub dot_graph: Option<String>,
    pub properties_checked: Vec<Arc<str>>,
    /// Under `--continue`: violations of `PROPERTY` action parts, counted by
    /// property, with up to ten of their traces. An initial-state violation always
    /// stops the check, as in TLC.
    pub violations_by_property: Vec<(Arc<str>, usize)>,
    pub property_violation_traces: Vec<PropertyViolation>,
}

#[derive(Debug)]
pub struct PropertyStats {
    pub name: Arc<str>,
    pub satisfied: usize,
    pub violated: usize,
    pub errors: usize,
    pub depth_satisfied: BTreeMap<usize, usize>,
    pub depth_total: BTreeMap<usize, usize>,
}

#[derive(Debug)]
pub enum CheckResult {
    Ok(CheckStats),
    InvariantViolation(Counterexample, CheckStats),
    RefinementViolation(RefinementViolation, CheckStats),
    LivenessViolation(LivenessViolation, CheckStats),
    PropertyViolation(PropertyViolation, CheckStats),
    Deadlock(Vec<State>, Vec<Option<Arc<str>>>, CheckStats),
    InitError(EvalError),
    NextError(EvalError, Vec<State>, Option<String>),
    InvariantError(EvalError, Vec<State>, Option<String>),
    LivenessError(LivenessError, CheckStats),
    MaxStatesExceeded(CheckStats),
    MaxDepthExceeded(CheckStats),
    MaxTimeExceeded(CheckStats),
    NoInitialStates,
    PrepareError(PrepareSpecError),
}

/// An error evaluating the spec while checking liveness, after the state search:
/// in the property `property`, or in the fairness constraints when it is `None`.
#[derive(Debug)]
pub struct LivenessError {
    pub property: Option<Arc<str>>,
    pub error: EvalError,
}

impl LivenessError {
    fn fairness(error: EvalError) -> Self {
        Self {
            property: None,
            error,
        }
    }

    fn property(name: &Arc<str>) -> impl FnOnce(EvalError) -> Self + '_ {
        move |error| Self {
            property: Some(name.clone()),
            error,
        }
    }
}

#[derive(Debug)]
pub enum PrepareSpecError {
    InstanceError(EvalError),
    MissingConstants(Vec<Arc<str>>),
    AssumeViolation(usize),
    AssumeError(usize, EvalError),
    NonModelValueSymmetry(Arc<str>, Vec<String>),
    RefinementConfigError(String),
    /// A liveness property the tableau checker cannot translate.
    LivenessProperty(String),
}

#[cfg(not(target_arch = "wasm32"))]
fn load_module_extends(
    name: &Arc<str>,
    spec_path: &std::path::Path,
    registry: &mut ModuleRegistry,
    domains: &mut crate::ast::Env,
    extended_defs: &mut Definitions,
    ancestors: &mut Vec<Arc<str>>,
) -> Result<(), EvalError> {
    if ancestors.iter().any(|a| a == name) {
        let mut cycle_path: Vec<String> = ancestors
            .iter()
            .skip_while(|a| a.as_ref() != name.as_ref())
            .map(|a| a.to_string())
            .collect();
        cycle_path.push(name.to_string());
        return Err(EvalError::DomainError {
            message: format!("cyclic EXTENDS dependency: {}", cycle_path.join(" -> ")),
            span: None,
        });
    }

    if let Some(cached) = registry.get(name) {
        for (def_name, def) in &cached.definitions {
            extended_defs.insert(def_name.clone(), def.clone());
        }
        return Ok(());
    }

    let (child_extends, child_defs) = match registry.load(name, spec_path) {
        Ok(loaded) => (loaded.extends.clone(), loaded.definitions.clone()),
        Err(ModuleError::NotFound(_)) => {
            return Err(EvalError::DomainError {
                message: format!(
                    "module {} not found (no file {}.tla in spec directory)",
                    name, name
                ),
                span: None,
            });
        }
        Err(ModuleError::ParseError(msg)) => {
            return Err(EvalError::DomainError {
                message: format!("parse error in module {}: {}", name, msg),
                span: None,
            });
        }
        Err(ModuleError::CyclicDependency(dep)) => {
            return Err(EvalError::DomainError {
                message: format!("cyclic dependency loading module {}", dep),
                span: None,
            });
        }
        Err(ModuleError::IoError(msg)) => {
            return Err(EvalError::DomainError {
                message: format!("I/O error loading module {}: {}", name, msg),
                span: None,
            });
        }
    };

    ancestors.push(name.clone());
    for ext in &child_extends {
        if stdlib::is_stdlib_module(ext) {
            stdlib::load_module(ext, domains);
        } else {
            load_module_extends(ext, spec_path, registry, domains, extended_defs, ancestors)?;
        }
    }
    ancestors.pop();

    for (def_name, def) in child_defs {
        extended_defs.insert(def_name, def);
    }

    Ok(())
}

pub fn prepare_spec(
    spec: &Spec,
    domains: &Env,
    #[cfg(not(target_arch = "wasm32"))] spec_path: Option<&PathBuf>,
    #[cfg(not(target_arch = "wasm32"))] quiet: bool,
) -> Result<(Env, Definitions), PrepareSpecError> {
    let user_constants = domains.clone();
    let mut domains = Env::new();
    stdlib::load_builtins(&mut domains);
    for module in &spec.extends {
        stdlib::load_module(module, &mut domains);
    }
    for (k, v) in user_constants {
        domains.insert(k, v);
    }

    let mut extended_defs: Definitions = BTreeMap::new();
    #[cfg(not(target_arch = "wasm32"))]
    if let Some(spec_path) = spec_path {
        let mut registry = ModuleRegistry::new();
        let mut ancestors: Vec<Arc<str>> = Vec::new();
        for module in &spec.extends {
            if stdlib::is_stdlib_module(module) {
                continue;
            }
            if let Err(err) = load_module_extends(
                module,
                spec_path,
                &mut registry,
                &mut domains,
                &mut extended_defs,
                &mut ancestors,
            ) {
                return Err(PrepareSpecError::InstanceError(err));
            }
        }
    }
    for (name, def) in &spec.definitions {
        extended_defs.insert(name.clone(), def.clone());
    }
    let defs = extended_defs;

    crate::config::bind_model_value_names(&mut domains, spec, &defs);

    for inst in &spec.instances {
        if stdlib::is_stdlib_module(&inst.module_name) {
            stdlib::load_module(&inst.module_name, &mut domains);
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    if !spec.instances.is_empty()
        && let Some(spec_path) = spec_path
    {
        let mut registry = ModuleRegistry::new();
        for inst in &spec.instances {
            if stdlib::is_stdlib_module(&inst.module_name) {
                continue;
            }
            match registry.load(&inst.module_name, spec_path) {
                Ok(_) => {}
                Err(e) => {
                    if !quiet {
                        eprintln!(
                            "  Warning: could not load module {}: {:?}",
                            inst.module_name, e
                        );
                    }
                }
            }
        }
        match resolve_instances(spec, &registry) {
            Ok((static_instances, param_instances, instance_vars)) => {
                let total = static_instances.len() + param_instances.len();
                if total > 0 && !quiet {
                    eprintln!("  Resolved {} instance(s)", total);
                }
                set_resolved_instances(static_instances);
                set_parameterized_instances(param_instances);
                crate::eval::set_resolved_instance_vars(instance_vars);
            }
            Err(e) => {
                if !quiet {
                    eprintln!("  Warning: could not resolve instances: {:?}", e);
                }
            }
        }
    }

    let missing: Vec<_> = spec
        .constants
        .iter()
        .filter(|c| !domains.contains_key(c))
        .cloned()
        .collect();
    if !missing.is_empty() {
        return Err(PrepareSpecError::MissingConstants(missing));
    }

    for (idx, assume) in spec.assumes.iter().enumerate() {
        match eval(assume, &mut domains, &defs) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Err(PrepareSpecError::AssumeViolation(idx)),
            Ok(_) => {
                return Err(PrepareSpecError::AssumeError(
                    idx,
                    EvalError::TypeMismatch {
                        expected: "Bool",
                        got: Value::Bool(false),
                        context: Some("ASSUME evaluation"),
                        span: None,
                    },
                ));
            }
            Err(e) => return Err(PrepareSpecError::AssumeError(idx, e)),
        }
    }

    Ok((domains, defs))
}

fn needs_liveness_check(spec: &Spec, config: &CheckerConfig) -> bool {
    config.check_liveness
        && (!spec.fairness.is_empty()
            || !spec.liveness_properties.is_empty()
            || !spec.quantified_fairness.is_empty())
}

/// The error [`check`] would report as `liveness_property_error`, found without a
/// state search: under the tableau engine every liveness property is translated, and
/// its tableau built, before exploring. `None` when there is none, or when the spec
/// cannot be prepared (missing constants, say), a failure `check` reports itself.
#[cfg(not(target_arch = "wasm32"))]
pub fn liveness_property_error(
    spec: &Spec,
    domains: &Env,
    config: &CheckerConfig,
) -> Option<String> {
    if config.liveness_engine != LivenessEngine::Tableau || !needs_liveness_check(spec, config) {
        return None;
    }
    crate::eval::set_symbolic_integers(config.symbolic_integers);
    let (domains, defs) =
        prepare_spec(spec, domains, config.spec_path.as_ref(), config.quiet).ok()?;
    tableau_properties(spec, &domains, &defs).err()
}

pub fn check(spec: &Spec, domains: &Env, config: &CheckerConfig) -> CheckResult {
    let _engine = crate::eval::EngineOverride::new(
        config.use_inference_engine,
        config.allow_unassigned_stutter,
    );
    crate::eval::set_symbolic_integers(config.symbolic_integers);
    crate::eval::set_enum_caps(crate::eval::EnumCaps {
        powerset: config.max_powerset,
        permutations: config.max_permutations,
        subbag: config.max_subbag_copies,
    });
    #[cfg(not(target_arch = "wasm32"))]
    let prep = prepare_spec(spec, domains, config.spec_path.as_ref(), config.quiet);
    #[cfg(target_arch = "wasm32")]
    let prep = prepare_spec(spec, domains);
    let (domains, defs) = match prep {
        Ok(r) => r,
        Err(e) => return CheckResult::PrepareError(e),
    };

    let mut symmetry = SymmetryConfig::new();
    for sym_const in &config.symmetric_constants {
        if let Some(Value::Set(elements)) = domains.get(sym_const) {
            let non_model: Vec<String> = elements
                .iter()
                .filter(|e| !matches!(e, Value::Model(_)))
                .map(format_value)
                .collect();
            if !non_model.is_empty() {
                return CheckResult::PrepareError(PrepareSpecError::NonModelValueSymmetry(
                    sym_const.clone(),
                    non_model,
                ));
            }
            symmetry.add_symmetric_set(elements.as_ref().clone());
        } else if !config.quiet {
            let available: Vec<_> = spec.constants.iter().map(|c| c.as_ref()).collect();
            eprintln!(
                "  Warning: --symmetry '{}' does not match any set constant (available: {})",
                sym_const,
                if available.is_empty() {
                    "none".to_string()
                } else {
                    available.join(", ")
                }
            );
        }
    }
    if !symmetry.is_empty() && !config.quiet {
        eprintln!(
            "  Symmetry reduction enabled for: {}",
            config
                .symmetric_constants
                .iter()
                .map(|s| s.as_ref())
                .collect::<Vec<_>>()
                .join(", ")
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

    let init_expr = match spec.init.as_ref() {
        Some(e) => e,
        None => {
            return CheckResult::InitError(EvalError::DomainError {
                message: "missing Init definition".to_string(),
                span: None,
            });
        }
    };
    let next_expr = match spec.next.as_ref() {
        Some(e) => e,
        None => {
            return CheckResult::NextError(
                EvalError::DomainError {
                    message: "missing Next definition".to_string(),
                    span: None,
                },
                vec![],
                None,
            );
        }
    };

    if !config.quiet {
        eprintln!("  Computing initial states...");
    }
    let initial = match init_states(init_expr, &spec.vars, &domains, &defs) {
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
    let mut parent_action: Vec<Option<Arc<str>>> = Vec::new();
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new();

    let needs_liveness_check = needs_liveness_check(spec, config);

    #[cfg(not(target_arch = "wasm32"))]
    let collect_edges =
        config.export_dot_path.is_some() || config.export_dot_string || needs_liveness_check;
    #[cfg(target_arch = "wasm32")]
    let collect_edges = config.export_dot_string || needs_liveness_check;
    let mut all_edges: Vec<EdgeList> = Vec::new();
    let mut renamed_successors: HashMap<(usize, usize), State> = HashMap::new();
    let mut stats = CheckStats {
        states_explored: 0,
        transitions: 0,
        transitions_by_action: BTreeMap::new(),
        max_depth_reached: 0,
        elapsed_secs: 0.0,
        violation_count: 0,
        violation_traces: Vec::new(),
        violations_by_invariant: Vec::new(),
        property_stats: Vec::new(),
        dot_graph: None,
        properties_checked: Vec::new(),
        violations_by_property: Vec::new(),
        property_violation_traces: Vec::new(),
    };

    let base_env: Env = domains.clone();
    let primed_vars = make_primed_names(&spec.vars);
    let mut reusable_env = base_env.clone();

    let refinement = match &config.check_refinement {
        Some(alias) => {
            if !config.symmetric_constants.is_empty() {
                return CheckResult::PrepareError(PrepareSpecError::RefinementConfigError(
                    "--check-refinement cannot be combined with --symmetry: symmetry reduction \
                     prunes symmetric transitions, so a refinement violation on a pruned sibling \
                     could be missed"
                        .to_string(),
                ));
            }
            match crate::refinement::RefinementSpec::resolve(alias, spec) {
                Ok(resolved) => Some(resolved),
                Err(message) => {
                    return CheckResult::PrepareError(PrepareSpecError::RefinementConfigError(
                        message,
                    ));
                }
            }
        }
        None => None,
    };

    let init_properties: Vec<(&Arc<str>, &Expr)> = spec
        .safety_properties
        .iter()
        .filter_map(|property| match property {
            SafetyProperty::Init { name, predicate } => Some((name, predicate)),
            SafetyProperty::Action { .. } => None,
        })
        .collect();
    let mut action_properties: Vec<ActionPropertyCheck> = Vec::new();
    for property in &spec.safety_properties {
        if let SafetyProperty::Action { name, formula } = property
            && let Err(e) =
                expand_action_property(name, formula, &domains, &defs, &mut action_properties)
        {
            return CheckResult::InitError(e);
        }
    }
    let mut successor_env = if action_properties.is_empty() {
        Env::new()
    } else {
        base_env.clone()
    };

    let tableau_properties =
        if needs_liveness_check && config.liveness_engine == LivenessEngine::Tableau {
            match tableau_properties(spec, &domains, &defs) {
                Ok(properties) => properties,
                Err(message) => {
                    return CheckResult::PrepareError(PrepareSpecError::LivenessProperty(message));
                }
            }
        } else {
            Vec::new()
        };

    let mut violation_counts_by_inv: Vec<usize> = vec![0; spec.invariants.len()];
    let mut excluded_checked: HashSet<State> = HashSet::new();
    let mut property_violation_counts: BTreeMap<Arc<str>, usize> = BTreeMap::new();
    let mut excluded_successors: Vec<Vec<State>> = Vec::new();
    let max_violation_traces: usize = 10;

    let count_exprs: Vec<(Arc<str>, Expr)> = config
        .count_properties
        .iter()
        .filter_map(|name| match defs.get(name) {
            Some((params, expr)) if params.is_empty() => Some((name.clone(), (**expr).clone())),
            Some(_) => {
                if !config.quiet {
                    eprintln!("  Warning: '{}' has parameters, skipping", name);
                }
                None
            }
            None => {
                if !config.quiet {
                    eprintln!("  Warning: '{}' not found in definitions, skipping", name);
                }
                None
            }
        })
        .collect();

    let mut property_counters: Vec<PropertyStats> = count_exprs
        .iter()
        .map(|(name, _)| PropertyStats {
            name: name.clone(),
            satisfied: 0,
            violated: 0,
            errors: 0,
            depth_satisfied: BTreeMap::new(),
            depth_total: BTreeMap::new(),
        })
        .collect();

    let state_passes_constraints =
        |state: &State, reusable_env: &mut Env| -> Result<bool, EvalError> {
            if config.state_constraints.is_empty() {
                return Ok(true);
            }
            for (i, var) in spec.vars.iter().enumerate() {
                if let Some(val) = state.values.get(i) {
                    reusable_env.insert(var.clone(), val.clone());
                }
            }
            for constraint in &config.state_constraints {
                match eval(constraint, reusable_env, &defs) {
                    Ok(Value::Bool(true)) => continue,
                    Ok(Value::Bool(false)) => return Ok(false),
                    Ok(other) => {
                        return Err(EvalError::type_mismatch_ctx("Bool", other, "CONSTRAINT"));
                    }
                    Err(e) => return Err(e),
                }
            }
            Ok(true)
        };

    let mut constraint_env = if config.state_constraints.is_empty() {
        Env::new()
    } else {
        base_env.clone()
    };

    for state in initial {
        let within_constraints = match state_passes_constraints(&state, &mut constraint_env) {
            Ok(passes) => passes,
            Err(e) => return CheckResult::InitError(e),
        };
        if !init_properties.is_empty() {
            if !config.continue_on_violation {
                match violated_invariants(spec, &state, &base_env, &defs) {
                    Ok(violated) => {
                        if let Some(&first) = violated.first() {
                            stats.elapsed_secs = elapsed_secs();
                            return CheckResult::InvariantViolation(
                                Counterexample {
                                    trace: vec![state.clone()],
                                    actions: vec![None],
                                    violated_invariant: first,
                                },
                                stats,
                            );
                        }
                    }
                    Err(e) => return CheckResult::InvariantError(e, vec![state.clone()], None),
                }
            }
            let mut env = base_env.clone();
            bind_state(&mut env, &spec.vars, &state);
            let init_ctx = EvalContext {
                state_vars: spec.vars.clone(),
            };
            for (name, predicate) in &init_properties {
                match eval_with_context(predicate, &mut env, &defs, &init_ctx) {
                    Ok(Value::Bool(true)) => {}
                    Ok(Value::Bool(false)) => {
                        stats.elapsed_secs = elapsed_secs();
                        return CheckResult::PropertyViolation(
                            PropertyViolation {
                                property: (*name).clone(),
                                kind: PropertyViolationKind::Init,
                                trace: vec![state.clone()],
                                actions: vec![None],
                            },
                            stats,
                        );
                    }
                    Ok(other) => {
                        return CheckResult::InitError(EvalError::type_mismatch_ctx(
                            "Bool", other, "PROPERTY",
                        ));
                    }
                    Err(e) => return CheckResult::InitError(e),
                }
            }
        }
        if !within_constraints {
            if spec.invariants.is_empty() || !excluded_checked.insert(state.clone()) {
                continue;
            }
            let violated = match violated_invariants(spec, &state, &base_env, &defs) {
                Ok(violated) => violated,
                Err(e) => return CheckResult::InvariantError(e, vec![state.clone()], None),
            };
            if let Some(&first) = violated.first() {
                if !config.continue_on_violation {
                    stats.elapsed_secs = elapsed_secs();
                    return CheckResult::InvariantViolation(
                        Counterexample {
                            trace: vec![state.clone()],
                            actions: vec![None],
                            violated_invariant: first,
                        },
                        stats,
                    );
                }
                for idx in violated {
                    violation_counts_by_inv[idx] += 1;
                    stats.violation_count += 1;
                    if stats.violation_traces.len() < max_violation_traces {
                        stats.violation_traces.push(Counterexample {
                            trace: vec![state.clone()],
                            actions: vec![None],
                            violated_invariant: idx,
                        });
                    }
                }
            }
            continue;
        }
        if let Some(refinement) = &refinement {
            match refinement.init_holds(&state, &spec.vars, &base_env, &defs) {
                Ok(true) => {}
                Ok(false) => {
                    stats.elapsed_secs = elapsed_secs();
                    return CheckResult::RefinementViolation(
                        RefinementViolation {
                            trace: vec![state.clone()],
                            actions: vec![None],
                            alias: refinement.alias(),
                            at_init: true,
                        },
                        stats,
                    );
                }
                Err(e) => return CheckResult::InitError(e),
            }
        }
        let canonical = symmetry.canonicalize(&state).into_owned();
        let (idx, is_new) = states.insert_full(canonical);
        if is_new {
            parent.push(None);
            parent_action.push(None);
            if collect_edges {
                all_edges.push(Vec::new());
            }
            queue.push_back((idx, 1));
        }
    }

    let reconstruct_trace = |state_idx: usize,
                             states: &IndexSet<State>,
                             parent: &[Option<usize>],
                             parent_action: &[Option<Arc<str>>]|
     -> (Vec<State>, Vec<Option<Arc<str>>>) {
        let mut trace = Vec::new();
        let mut actions = Vec::new();
        let mut idx = Some(state_idx);
        while let Some(i) = idx {
            let Some(state) = states.get_index(i) else {
                break;
            };
            trace.push(state.clone());
            actions.push(parent_action[i].clone());
            idx = parent[i];
        }
        trace.reverse();
        actions.reverse();
        (trace, actions)
    };

    let do_export = |states: &IndexSet<State>,
                     parent: &[Option<usize>],
                     error_state: Option<usize>,
                     all_edges: &[EdgeList]|
     -> Option<String> {
        let trace_path: Vec<usize> = if let Some(idx) = error_state {
            let mut path = Vec::new();
            let mut current = Some(idx);
            while let Some(i) = current {
                path.push(i);
                current = parent[i];
            }
            path.reverse();
            path
        } else {
            Vec::new()
        };
        let dot_ctx = DotExport {
            states,
            parents: parent,
            vars: &spec.vars,
            error_state,
            all_edges,
            trace_path: &trace_path,
            mode: config.dot_mode,
        };
        #[cfg(not(target_arch = "wasm32"))]
        if let Some(ref path) = config.export_dot_path {
            match File::create(path) {
                Ok(file) => {
                    let mut writer = BufWriter::new(file);
                    if let Err(e) = export_dot(&dot_ctx, &mut writer) {
                        eprintln!("  Failed to write DOT export: {}", e);
                    } else {
                        eprintln!("  Exported state graph to {}", path.display());
                    }
                }
                Err(e) => eprintln!("  Failed to create DOT file: {}", e),
            }
        }
        if config.export_dot_string {
            let mut buf = Vec::new();
            if export_dot(&dot_ctx, &mut buf).is_ok() {
                return String::from_utf8(buf).ok();
            }
        }
        None
    };

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
                    stats.states_explored,
                    queue.len()
                );
            } else {
                let elapsed = elapsed_secs();
                let rate = stats.states_explored as f64 / elapsed.max(0.001);
                eprintln!(
                    "  {} states explored | {:.0}/s | depth: {} | queue: {}",
                    stats.states_explored,
                    rate,
                    depth,
                    queue.len()
                );
            }
        }

        if stats.states_explored > config.max_states {
            stats.elapsed_secs = elapsed_secs();
            stats.dot_graph = do_export(&states, &parent, None, &all_edges);
            return CheckResult::MaxStatesExceeded(stats);
        }

        if depth > config.max_depth {
            stats.elapsed_secs = elapsed_secs();
            stats.dot_graph = do_export(&states, &parent, None, &all_edges);
            return CheckResult::MaxDepthExceeded(stats);
        }

        if let Some(max_secs) = config.max_seconds
            && elapsed_secs() as u64 >= max_secs
        {
            stats.elapsed_secs = elapsed_secs();
            stats.dot_graph = do_export(&states, &parent, None, &all_edges);
            return CheckResult::MaxTimeExceeded(stats);
        }

        let Some(current) = states.get_index(current_idx) else {
            return CheckResult::NextError(
                EvalError::DomainError {
                    message: format!("internal: invalid state index {}", current_idx),
                    span: None,
                },
                vec![],
                None,
            );
        };
        let mut env = base_env.clone();
        for (i, var) in spec.vars.iter().enumerate() {
            if let Some(val) = current.values.get(i) {
                env.insert(var.clone(), val.clone());
            }
        }

        let ctx = EvalContext {
            state_vars: spec.vars.clone(),
        };

        for (idx, invariant) in spec.invariants.iter().enumerate() {
            match eval_with_context(invariant, &mut env, &defs, &ctx) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    if config.continue_on_violation {
                        violation_counts_by_inv[idx] += 1;
                        stats.violation_count += 1;
                        if stats.violation_traces.len() < max_violation_traces {
                            let (trace, actions) =
                                reconstruct_trace(current_idx, &states, &parent, &parent_action);
                            stats.violation_traces.push(Counterexample {
                                trace,
                                actions,
                                violated_invariant: idx,
                            });
                        }
                    } else {
                        let (trace, actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        stats.elapsed_secs = elapsed_secs();
                        stats.dot_graph =
                            do_export(&states, &parent, Some(current_idx), &all_edges);
                        return CheckResult::InvariantViolation(
                            Counterexample {
                                trace,
                                actions,
                                violated_invariant: idx,
                            },
                            stats,
                        );
                    }
                }
                Ok(_) => {
                    let (trace, _actions) =
                        reconstruct_trace(current_idx, &states, &parent, &parent_action);
                    let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                    return CheckResult::InvariantError(
                        EvalError::TypeMismatch {
                            expected: "Bool",
                            got: Value::Bool(false),
                            context: Some("invariant evaluation"),
                            span: None,
                        },
                        trace,
                        dot,
                    );
                }
                Err(e) => {
                    let (trace, _actions) =
                        reconstruct_trace(current_idx, &states, &parent, &parent_action);
                    let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                    return CheckResult::InvariantError(e, trace, dot);
                }
            }
        }

        if !count_exprs.is_empty() {
            for (idx, (_name, expr)) in count_exprs.iter().enumerate() {
                let entry = &mut property_counters[idx];
                *entry.depth_total.entry(depth).or_default() += 1;
                match eval_with_context(expr, &mut env, &defs, &ctx) {
                    Ok(Value::Bool(true)) => {
                        entry.satisfied += 1;
                        *entry.depth_satisfied.entry(depth).or_default() += 1;
                    }
                    Ok(Value::Bool(false)) => entry.violated += 1,
                    _ => entry.errors += 1,
                }
            }
        }

        let Some(current) = states.get_index(current_idx) else {
            continue;
        };
        let successors = match next_states(
            next_expr,
            current,
            &spec.vars,
            &primed_vars,
            &mut reusable_env,
            &defs,
        ) {
            Ok(s) => s,
            Err(e) => {
                let (trace, _actions) =
                    reconstruct_trace(current_idx, &states, &parent, &parent_action);
                let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                return CheckResult::NextError(e, trace, dot);
            }
        };

        if successors.is_empty() && !config.allow_deadlock {
            let (trace, actions) = reconstruct_trace(current_idx, &states, &parent, &parent_action);
            stats.elapsed_secs = elapsed_secs();
            stats.dot_graph = do_export(&states, &parent, Some(current_idx), &all_edges);
            return CheckResult::Deadlock(trace, actions, stats);
        }

        for transition in successors {
            stats.transitions += 1;
            *stats
                .transitions_by_action
                .entry(transition.action.clone())
                .or_insert(0) += 1;
            if !action_properties.is_empty() {
                match violated_action_property(
                    &action_properties,
                    &mut env,
                    &mut successor_env,
                    &primed_vars,
                    &transition.state,
                    &defs,
                    &ctx,
                ) {
                    Ok(violated) if violated.is_empty() => {}
                    Ok(violated) => {
                        let (mut trace, mut actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        trace.push(transition.state.clone());
                        actions.push(transition.action.clone());
                        let mut violations = violated.into_iter().map(|name| PropertyViolation {
                            property: name.clone(),
                            kind: PropertyViolationKind::Action,
                            trace: trace.clone(),
                            actions: actions.clone(),
                        });
                        if !config.continue_on_violation
                            && let Some(first) = violations.next()
                        {
                            stats.elapsed_secs = elapsed_secs();
                            return CheckResult::PropertyViolation(first, stats);
                        }
                        for violation in violations {
                            record_property_violation(
                                &mut stats,
                                &mut property_violation_counts,
                                violation,
                                max_violation_traces,
                            );
                        }
                    }
                    Err(e) => {
                        let (trace, _actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                        return CheckResult::NextError(e, trace, dot);
                    }
                }
            }
            match state_passes_constraints(&transition.state, &mut constraint_env) {
                Ok(true) => {}
                Ok(false) => {
                    if needs_liveness_check {
                        if excluded_successors.len() <= current_idx {
                            excluded_successors.resize_with(current_idx + 1, Vec::new);
                        }
                        excluded_successors[current_idx].push(transition.state.clone());
                    }
                    if spec.invariants.is_empty()
                        || !excluded_checked.insert(transition.state.clone())
                    {
                        continue;
                    }
                    let violated = violated_invariants(spec, &transition.state, &base_env, &defs);
                    let with_successor = || {
                        let (mut trace, mut actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        trace.push(transition.state.clone());
                        actions.push(transition.action.clone());
                        (trace, actions)
                    };
                    let violated = match violated {
                        Ok(violated) => violated,
                        Err(e) => {
                            let (trace, _actions) = with_successor();
                            let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                            return CheckResult::InvariantError(e, trace, dot);
                        }
                    };
                    if let Some(&first) = violated.first() {
                        let (trace, actions) = with_successor();
                        if !config.continue_on_violation {
                            stats.elapsed_secs = elapsed_secs();
                            stats.dot_graph =
                                do_export(&states, &parent, Some(current_idx), &all_edges);
                            return CheckResult::InvariantViolation(
                                Counterexample {
                                    trace,
                                    actions,
                                    violated_invariant: first,
                                },
                                stats,
                            );
                        }
                        for idx in violated {
                            violation_counts_by_inv[idx] += 1;
                            stats.violation_count += 1;
                            if stats.violation_traces.len() < max_violation_traces {
                                stats.violation_traces.push(Counterexample {
                                    trace: trace.clone(),
                                    actions: actions.clone(),
                                    violated_invariant: idx,
                                });
                            }
                        }
                    }
                    continue;
                }
                Err(e) => {
                    let (trace, _actions) =
                        reconstruct_trace(current_idx, &states, &parent, &parent_action);
                    let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                    return CheckResult::NextError(e, trace, dot);
                }
            }
            if let Some(refinement) = &refinement
                && let Some(from) = states.get_index(current_idx)
            {
                match refinement.step_refines(from, &transition.state, &spec.vars, &base_env, &defs)
                {
                    Ok(true) => {}
                    Ok(false) => {
                        let (mut trace, mut actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        trace.push(transition.state.clone());
                        actions.push(transition.action.clone());
                        stats.elapsed_secs = elapsed_secs();
                        return CheckResult::RefinementViolation(
                            RefinementViolation {
                                trace,
                                actions,
                                alias: refinement.alias(),
                                at_init: false,
                            },
                            stats,
                        );
                    }
                    Err(e) => {
                        let (trace, _actions) =
                            reconstruct_trace(current_idx, &states, &parent, &parent_action);
                        let dot = do_export(&states, &parent, Some(current_idx), &all_edges);
                        return CheckResult::NextError(e, trace, dot);
                    }
                }
            }
            let canonical = symmetry.canonicalize(&transition.state).into_owned();
            if collect_edges && !symmetry.is_empty() && canonical != transition.state {
                renamed_successors.insert(
                    (current_idx, all_edges[current_idx].len()),
                    transition.state.clone(),
                );
            }
            let (succ_idx, is_new) = states.insert_full(canonical);
            if is_new {
                parent.push(Some(current_idx));
                parent_action.push(transition.action.clone());
                if collect_edges {
                    all_edges.push(Vec::new());
                }
                queue.push_back((succ_idx, depth + 1));
            }
            if collect_edges {
                all_edges[current_idx].push((succ_idx, transition.action));
            }
        }
    }

    stats.elapsed_secs = elapsed_secs();
    stats.dot_graph = do_export(&states, &parent, None, &all_edges);

    if config.continue_on_violation {
        stats.violations_by_invariant = violation_counts_by_inv
            .iter()
            .enumerate()
            .filter(|(_, count)| **count > 0)
            .map(|(idx, count)| {
                let count = *count;
                let name = spec.invariant_names.get(idx).and_then(|n| n.clone());
                (name, count)
            })
            .collect();
    }

    stats.property_stats = property_counters;
    stats.violations_by_property = property_violation_counts.into_iter().collect();
    stats.properties_checked = properties_checked(spec, config, &stats);

    if needs_liveness_check {
        if !config.quiet {
            eprintln!("  Running liveness checking...");
        }
        let ctx = LivenessContext {
            spec,
            domains: &domains,
            defs: &defs,
            config,
            excluded_successors: &excluded_successors,
            renamed_successors: &renamed_successors,
            tableau_properties: &tableau_properties,
        };
        match check_liveness_properties(ctx, &states, &parent, &all_edges, &elapsed_secs) {
            Ok(LivenessCheckOutcome::Ok) => {}
            Ok(LivenessCheckOutcome::Violation(violation)) => {
                return CheckResult::LivenessViolation(violation, stats);
            }
            Ok(LivenessCheckOutcome::TimeExceeded) => {
                stats.elapsed_secs = elapsed_secs();
                stats.dot_graph = do_export(&states, &parent, None, &all_edges);
                return CheckResult::MaxTimeExceeded(stats);
            }
            Err(error) => {
                stats.elapsed_secs = elapsed_secs();
                return CheckResult::LivenessError(error, stats);
            }
        }
    }

    CheckResult::Ok(stats)
}

/// Every invariant a state violates. Used for states outside the `CONSTRAINT`,
/// which TLC checks against the invariants but does not explore.
fn violated_invariants(
    spec: &Spec,
    state: &State,
    base_env: &Env,
    defs: &Definitions,
) -> Result<Vec<usize>, EvalError> {
    if spec.invariants.is_empty() {
        return Ok(Vec::new());
    }
    let mut env = base_env.clone();
    bind_state(&mut env, &spec.vars, state);
    let ctx = EvalContext {
        state_vars: spec.vars.clone(),
    };
    let mut violated = Vec::new();
    for (idx, invariant) in spec.invariants.iter().enumerate() {
        match eval_with_context(invariant, &mut env, defs, &ctx)? {
            Value::Bool(true) => {}
            Value::Bool(false) => violated.push(idx),
            other => {
                return Err(EvalError::type_mismatch_ctx(
                    "Bool",
                    other,
                    "invariant evaluation",
                ));
            }
        }
    }
    Ok(violated)
}

struct ActionPropertyCheck {
    name: Arc<str>,
    action: Expr,
    subscript: Expr,
}

/// Instantiate each `\A x \in S` around a `[][A]_v` property into concrete
/// action/subscript pairs, so a subscript may depend on the bound variable.
fn expand_action_property(
    name: &Arc<str>,
    formula: &Expr,
    domains: &Env,
    defs: &Definitions,
    out: &mut Vec<ActionPropertyCheck>,
) -> Result<(), EvalError> {
    match formula {
        Expr::Forall(var, domain, body) => {
            for element in quantifier_elements(domain, domains, defs)? {
                let subs = [(var.clone(), Expr::Lit(element))];
                let concrete = crate::substitution::substitute_expr(body, &subs);
                expand_action_property(name, &concrete, domains, defs, out)?;
            }
            Ok(())
        }
        Expr::BoxAction(action, subscript) => {
            out.push(ActionPropertyCheck {
                name: name.clone(),
                action: (**action).clone(),
                subscript: (**subscript).clone(),
            });
            Ok(())
        }
        other => Err(EvalError::domain_error(format!(
            "internal: PROPERTY '{name}' has an action part that is not [][A]_v: {other:?}"
        ))),
    }
}

fn bind_state(env: &mut Env, names: &[Arc<str>], state: &State) {
    for (name, value) in names.iter().zip(&state.values) {
        env.insert(name.clone(), value.clone());
    }
}

/// Every `[][A]_v` property the transition breaks: an `A`-step is required only
/// when the transition changes `v`. `env` holds the current state (`ctx`) and gets
/// the successor bound to the primed names; `successor_env` holds the successor alone.
fn violated_action_property<'a>(
    properties: &'a [ActionPropertyCheck],
    env: &mut Env,
    successor_env: &mut Env,
    primed_vars: &[Arc<str>],
    successor: &State,
    defs: &Definitions,
    ctx: &EvalContext,
) -> Result<Vec<&'a Arc<str>>, EvalError> {
    bind_state(env, primed_vars, successor);
    bind_state(successor_env, &ctx.state_vars, successor);
    let mut violated = Vec::new();
    for property in properties {
        if eval(&property.subscript, env, defs)? == eval(&property.subscript, successor_env, defs)?
        {
            continue;
        }
        match eval_with_context(&property.action, env, defs, ctx)? {
            Value::Bool(true) => {}
            Value::Bool(false) => violated.push(&property.name),
            other => return Err(EvalError::type_mismatch_ctx("Bool", other, "PROPERTY")),
        }
    }
    Ok(violated)
}

fn record_property_violation(
    stats: &mut CheckStats,
    counts: &mut BTreeMap<Arc<str>, usize>,
    violation: PropertyViolation,
    max_traces: usize,
) {
    *counts.entry(violation.property.clone()).or_default() += 1;
    stats.violation_count += 1;
    if stats.property_violation_traces.len() < max_traces {
        stats.property_violation_traces.push(violation);
    }
}

/// The cfg `PROPERTY` names whose every part was checked without a recorded
/// violation, plus the `*Spec` definitions whose temporal conjuncts were checked in
/// the legacy mode.
fn properties_checked(spec: &Spec, config: &CheckerConfig, stats: &CheckStats) -> Vec<Arc<str>> {
    let has_liveness = |name: &Arc<str>| spec.liveness_properties.iter().any(|p| &p.name == name);
    let violated = |name: &Arc<str>| {
        stats
            .violations_by_invariant
            .iter()
            .any(|(n, _)| n.as_ref() == Some(name))
            || stats.violations_by_property.iter().any(|(n, _)| n == name)
    };
    let mut names: Vec<Arc<str>> = config
        .properties
        .iter()
        .filter(|name| (config.check_liveness || !has_liveness(name)) && !violated(name))
        .cloned()
        .collect();
    if config.check_liveness {
        for property in spec
            .liveness_properties
            .iter()
            .filter(|p| p.from_specification)
        {
            if !names.contains(&property.name) {
                names.push(property.name.clone());
            }
        }
    }
    names
}

enum LivenessCheckOutcome {
    Ok,
    Violation(LivenessViolation),
    TimeExceeded,
}

struct LivenessContext<'a> {
    spec: &'a Spec,
    domains: &'a Env,
    defs: &'a Definitions,
    config: &'a CheckerConfig,
    excluded_successors: &'a [Vec<State>],
    renamed_successors: &'a HashMap<(usize, usize), State>,
    tableau_properties: &'a [TableauProperty],
}

fn check_liveness_properties(
    ctx: LivenessContext<'_>,
    states: &IndexSet<State>,
    parent: &[Option<usize>],
    all_edges: &[EdgeList],
    elapsed_secs: &dyn Fn() -> f64,
) -> Result<LivenessCheckOutcome, LivenessError> {
    let LivenessContext {
        spec,
        domains,
        defs,
        config,
        excluded_successors,
        renamed_successors,
        tableau_properties,
    } = ctx;
    let time_exceeded = || match config.max_seconds {
        Some(max_secs) => elapsed_secs() as u64 >= max_secs,
        None => false,
    };

    let mut graph = StateGraph::new();

    for (idx, state) in states.iter().enumerate() {
        graph.add_state(state.clone(), parent[idx]);
    }

    if !config.quiet {
        eprintln!(
            "  Reusing {} collected forward edge lists...",
            all_edges.len()
        );
    }

    for (state_idx, edges) in all_edges.iter().enumerate() {
        if time_exceeded() {
            return Ok(LivenessCheckOutcome::TimeExceeded);
        }

        for (position, (succ_idx, action)) in edges.iter().enumerate() {
            match renamed_successors.get(&(state_idx, position)) {
                Some(reached) => {
                    graph.add_renamed_edge(state_idx, *succ_idx, action.clone(), reached.clone())
                }
                None => graph.add_edge(state_idx, *succ_idx, action.clone()),
            }
        }
    }

    if time_exceeded() {
        return Ok(LivenessCheckOutcome::TimeExceeded);
    }

    let stutter_targets: Vec<usize> = (0..graph.state_count())
        .filter(|&idx| {
            !graph
                .successors(idx)
                .iter()
                .any(|e| e.target == idx && e.renamed.is_none())
        })
        .collect();
    for idx in stutter_targets {
        graph.add_edge(idx, idx, None);
    }

    let fairness = expand_fairness(spec, domains, defs).map_err(LivenessError::fairness)?;
    if config.liveness_engine == LivenessEngine::Tableau {
        let table = liveness::FairnessTable::build(
            &graph,
            &fairness,
            excluded_successors,
            &spec.vars,
            domains,
            defs,
        )
        .map_err(LivenessError::fairness)?;
        return tableau_liveness(
            spec,
            domains,
            defs,
            tableau_properties,
            &graph,
            &table,
            &time_exceeded,
        );
    }
    let mut liveness_properties = Vec::new();
    for property in &spec.liveness_properties {
        expand_liveness(
            &property.name,
            &property.formula,
            domains,
            defs,
            &mut liveness_properties,
        )
        .map_err(LivenessError::property(&property.name))?;
    }
    let table = liveness::FairnessTable::build(
        &graph,
        &fairness,
        excluded_successors,
        &spec.vars,
        domains,
        defs,
    )
    .map_err(LivenessError::fairness)?;

    for (name, property) in &liveness_properties {
        if time_exceeded() {
            return Ok(LivenessCheckOutcome::TimeExceeded);
        }
        if let Some(lasso) =
            liveness::find_violation(&graph, &table, property, &spec.vars, domains, defs)
                .map_err(LivenessError::property(name))?
        {
            let states_at = |indices: &[usize]| -> Vec<State> {
                indices
                    .iter()
                    .filter_map(|&idx| graph.get_state(idx).cloned())
                    .collect()
            };
            let violation = LivenessViolation {
                prefix: states_at(&lasso.prefix),
                cycle: states_at(&lasso.cycle),
                property: name.to_string(),
                fairness_info: table.fairness_info(&graph, &lasso.cycle),
            };
            return Ok(LivenessCheckOutcome::Violation(violation));
        }
    }

    Ok(LivenessCheckOutcome::Ok)
}

/// A liveness property as the tableau checker searches it: the negation of the
/// property conjoined with the specification's temporal assumptions, compiled.
struct TableauProperty {
    name: Arc<str>,
    violation: crate::ltl_check::Compiled,
    atoms: crate::ltl::AtomTable,
}

/// The tableau formulas of the liveness properties, built before the state search
/// so a property the tableau checker cannot express is reported up front. The
/// `WF`/`SF` parts a legacy `*Spec` extraction leaves in a quantified formula are
/// fairness, already applied, not obligations; in a cfg `PROPERTY` they are
/// obligations and stay.
fn tableau_properties(
    spec: &Spec,
    domains: &Env,
    defs: &Definitions,
) -> Result<Vec<TableauProperty>, String> {
    spec.liveness_properties
        .iter()
        .filter_map(|property| {
            if property.from_specification {
                crate::ast::without_fairness(&property.formula).map(|formula| (property, formula))
            } else {
                Some((property, property.formula.clone()))
            }
        })
        .map(|(property, formula)| {
            let formula = if crate::ast::has_temporal_operator(&formula) {
                formula
            } else {
                Expr::Always(Box::new(Expr::Eventually(Box::new(formula))))
            };
            let mut atoms = crate::ltl::AtomTable::new();
            let mut domain = |set: &Expr| {
                quantifier_elements(set, domains, defs).map_err(|e| format_eval_error(&e))
            };
            let mut builder = crate::ltl::Builder {
                atoms: &mut atoms,
                defs,
                domain: &mut domain,
            };
            let describe = |e: String| format!("PROPERTY '{}': {e}", property.name);
            let mut conjuncts = vec![builder.build(&formula, false).map_err(describe)?];
            for assumption in &spec.temporal_assumptions {
                conjuncts.push(builder.build(assumption, true).map_err(describe)?);
            }
            let violation = crate::ltl_check::compile(&crate::ltl::Ltl::And(conjuncts), &atoms)
                .map_err(describe)?;
            Ok(TableauProperty {
                name: property.name.clone(),
                violation,
                atoms,
            })
        })
        .collect()
}

/// Each liveness property checked by searching for a fair behavior that satisfies
/// the specification's temporal assumptions and violates the property.
fn tableau_liveness(
    spec: &Spec,
    domains: &Env,
    defs: &Definitions,
    properties: &[TableauProperty],
    graph: &StateGraph,
    table: &liveness::FairnessTable,
    time_exceeded: &dyn Fn() -> bool,
) -> Result<LivenessCheckOutcome, LivenessError> {
    let model = crate::ltl_check::Model {
        vars: &spec.vars,
        constants: domains,
        defs,
    };
    for property in properties {
        if time_exceeded() {
            return Ok(LivenessCheckOutcome::TimeExceeded);
        }
        let search = crate::ltl_check::find_behavior(
            graph,
            table,
            &property.violation,
            &property.atoms,
            &model,
            time_exceeded,
        )
        .map_err(LivenessError::property(&property.name))?;
        match search {
            crate::ltl_check::Search::Clean => {}
            crate::ltl_check::Search::OutOfTime => {
                return Ok(LivenessCheckOutcome::TimeExceeded);
            }
            crate::ltl_check::Search::Violation(lasso, fairness_info) => {
                let states_at = |indices: &[usize]| -> Vec<State> {
                    indices
                        .iter()
                        .filter_map(|&idx| graph.get_state(idx).cloned())
                        .collect()
                };
                return Ok(LivenessCheckOutcome::Violation(LivenessViolation {
                    prefix: states_at(&lasso.prefix),
                    cycle: states_at(&lasso.cycle),
                    property: property.name.to_string(),
                    fairness_info,
                }));
            }
        }
    }
    Ok(LivenessCheckOutcome::Ok)
}

fn quantifier_elements(
    domain: &Expr,
    domains: &Env,
    defs: &Definitions,
) -> Result<Vec<Value>, EvalError> {
    let mut env = domains.clone();
    match eval(domain, &mut env, defs)? {
        Value::Set(set) => Ok(set.iter().cloned().collect()),
        other => Err(EvalError::domain_error(format!(
            "quantified fairness/liveness domain must evaluate to a set, got {other:?}"
        ))),
    }
}

fn expand_fairness(
    spec: &Spec,
    domains: &Env,
    defs: &Definitions,
) -> Result<Vec<crate::ast::FairnessConstraint>, EvalError> {
    let mut fairness = spec.fairness.clone();
    let mut pending = spec.quantified_fairness.clone();
    while let Some((var, domain, body)) = pending.pop() {
        for element in quantifier_elements(&domain, domains, defs)? {
            let subs = [(var.clone(), Expr::Lit(element))];
            let concrete = crate::substitution::substitute_expr(&body, &subs);
            crate::ast::collect_temporal(
                &concrete,
                &mut fairness,
                &mut Vec::new(),
                &mut pending,
                &mut Vec::new(),
            );
        }
    }
    Ok(fairness)
}

/// Instantiate each `\A x \in S : body` of a liveness property into the forms
/// `liveness::find_violation` checks, keeping the property's name on every instance.
fn expand_liveness(
    name: &Arc<str>,
    formula: &Expr,
    domains: &Env,
    defs: &Definitions,
    out: &mut Vec<(Arc<str>, Expr)>,
) -> Result<(), EvalError> {
    match formula {
        Expr::Forall(var, domain, body) if crate::ast::expr_contains_temporal(body) => {
            for element in quantifier_elements(domain, domains, defs)? {
                let subs = [(var.clone(), Expr::Lit(element))];
                let concrete = crate::substitution::substitute_expr(body, &subs);
                let mut instances = Vec::new();
                crate::ast::collect_temporal(
                    &concrete,
                    &mut Vec::new(),
                    &mut instances,
                    &mut Vec::new(),
                    &mut Vec::new(),
                );
                for instance in &instances {
                    expand_liveness(name, instance, domains, defs, out)?;
                }
            }
            Ok(())
        }
        _ => {
            out.push((name.clone(), formula.clone()));
            Ok(())
        }
    }
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
    format_trace_with_actions(trace, &[], vars)
}

pub fn format_trace_with_actions(
    trace: &[State],
    actions: &[Option<Arc<str>>],
    vars: &[Arc<str>],
) -> String {
    if trace.is_empty() {
        return String::new();
    }

    let max_var_len = vars.iter().map(|v| v.len()).max().unwrap_or(0);
    let total_states = trace.len();
    let last_idx = total_states - 1;

    let mut out = String::new();
    for (i, state) in trace.iter().enumerate() {
        let prev = if i > 0 { Some(&trace[i - 1]) } else { None };

        if i == last_idx && total_states > 1 {
            out.push_str(&format!("State {} of {} [FINAL]\n", i, last_idx));
        } else if total_states > 1 {
            out.push_str(&format!("State {} of {}\n", i, last_idx));
        } else {
            out.push_str(&format!("State {}\n", i));
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

        if i < last_idx {
            let action_name = actions
                .get(i + 1)
                .and_then(|a| a.as_ref())
                .map(|s| s.as_ref())
                .unwrap_or("(unnamed)");
            out.push_str(&format!("\n  --[ {} ]-->\n\n", action_name));
        }
    }
    out
}

fn is_tla_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub fn format_value(val: &Value) -> String {
    match val {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Model(m) => m.to_string(),
        Value::IntSet(d) => d.name().to_string(),
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
            if r.keys().all(|k| is_tla_identifier(k)) {
                let fields: Vec<_> = r
                    .iter()
                    .map(|(k, v)| format!("{} |-> {}", k, format_value(v)))
                    .collect();
                format!("[{}]", fields.join(", "))
            } else {
                let pairs: Vec<_> = r
                    .iter()
                    .map(|(k, v)| format!("\"{}\" :> {}", k, format_value(v)))
                    .collect();
                format!("({})", pairs.join(" @@ "))
            }
        }
        Value::Tuple(t) => {
            let elems: Vec<_> = t.iter().map(format_value).collect();
            format!("<<{}>>", elems.join(", "))
        }
    }
}

pub fn format_eval_error(err: &EvalError) -> String {
    match err {
        EvalError::NotEnumerable { var, source, .. } => format!(
            "cannot enumerate the values of `{}'`\n  note: the only source for it is {}\n               help: give `{}'` a value directly, or draw it from a set the checker can enumerate",
            var, source, var
        ),
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
        Value::Model(_) => "ModelValue",
        Value::Set(_) | Value::IntSet(_) => "Set",
        Value::Fn(_) => "Function",
        Value::Record(_) => "Record",
        Value::Tuple(_) => "Sequence",
    }
}

pub fn eval_error_to_diagnostic(err: &EvalError) -> crate::diagnostic::Diagnostic {
    use crate::diagnostic::Diagnostic;
    let diag = match err {
        EvalError::NotEnumerable { var, source, .. } => {
            Diagnostic::error(format!("cannot enumerate the values of `{}`", var))
                .with_note(format!("the only source for it is {}", source))
                .with_help(format!(
                    "bind `{}` directly, or draw it from a set the checker can enumerate",
                    var
                ))
        }
        EvalError::UndefinedVar {
            name, suggestion, ..
        } => {
            let mut diag = Diagnostic::error(format!("undefined variable `{}`", name));
            if let Some(s) = suggestion {
                diag = diag.with_help(format!("did you mean `{}`?", s));
            }
            diag
        }
        EvalError::TypeMismatch {
            expected,
            got,
            context,
            ..
        } => {
            let type_name = value_type_name(got);
            let msg = if let Some(ctx) = context {
                format!(
                    "type mismatch in {}: expected {}, got {}",
                    ctx, expected, type_name
                )
            } else {
                format!("type mismatch: expected {}, got {}", expected, type_name)
            };
            Diagnostic::error(msg).with_note(format!("value was: {}", format_value(got)))
        }
        EvalError::DivisionByZero { .. } => Diagnostic::error("division by zero"),
        EvalError::EmptyChoose { .. } => Diagnostic::error("CHOOSE found no satisfying value")
            .with_help("the domain may be empty or no element satisfies the predicate"),
        EvalError::DomainError { message, .. } => Diagnostic::error(message.clone()),
    };
    if let Some(span) = err.span() {
        diag.with_span(span)
    } else {
        diag
    }
}

fn json_string(s: &str) -> String {
    serde_json::Value::String(s.to_string()).to_string()
}

pub fn value_to_json(val: &Value) -> String {
    match val {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Str(s) => json_string(s),
        Value::Model(m) => format!("{{\"model_value\": {}}}", json_string(m)),
        Value::IntSet(d) => format!("{{\"symbolic_set\": \"{}\"}}", d.name()),
        Value::Set(s) => {
            let elems: Vec<_> = s.iter().map(value_to_json).collect();
            format!("[{}]", elems.join(", "))
        }
        Value::Fn(f) => {
            let pairs: Vec<_> = f
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{{\"key\": {}, \"value\": {}}}",
                        value_to_json(k),
                        value_to_json(v)
                    )
                })
                .collect();
            format!("[{}]", pairs.join(", "))
        }
        Value::Record(r) => {
            let fields: Vec<_> = r
                .iter()
                .map(|(k, v)| format!("{}: {}", json_string(k), value_to_json(v)))
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
            state
                .values
                .get(i)
                .map(|val| format!("{}: {}", json_string(var), value_to_json(val)))
        })
        .collect();
    format!("{{{}}}", fields.join(", "))
}

pub fn trace_to_json(trace: &[State], vars: &[Arc<str>]) -> String {
    trace_to_json_with_actions(trace, &[], vars)
}

pub fn trace_to_json_with_actions(
    trace: &[State],
    actions: &[Option<Arc<str>>],
    vars: &[Arc<str>],
) -> String {
    let states: Vec<_> = trace
        .iter()
        .enumerate()
        .map(|(i, state)| {
            let action_str = actions
                .get(i)
                .and_then(|a| a.as_ref())
                .map(|s| json_string(s))
                .unwrap_or_else(|| "null".to_string());
            format!(
                "{{\"index\": {}, \"action\": {}, \"state\": {}}}",
                i,
                action_str,
                state_to_json(state, vars)
            )
        })
        .collect();
    format!("[{}]", states.join(", "))
}

fn is_boolean_shaped(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Lit(Value::Bool(_))
            | Expr::And(_, _)
            | Expr::Or(_, _)
            | Expr::Not(_)
            | Expr::Implies(_, _)
            | Expr::Equiv(_, _)
            | Expr::Eq(_, _)
            | Expr::Neq(_, _)
            | Expr::Lt(_, _)
            | Expr::Le(_, _)
            | Expr::Gt(_, _)
            | Expr::Ge(_, _)
            | Expr::In(_, _)
            | Expr::NotIn(_, _)
            | Expr::Subset(_, _)
            | Expr::ProperSubset(_, _)
            | Expr::SqSubseteq(_, _)
            | Expr::BagIn(_, _)
            | Expr::IsABag(_)
            | Expr::IsFiniteSet(_)
            | Expr::Forall(_, _, _)
            | Expr::Exists(_, _, _)
    )
}

fn predicate_is_used(spec: &Spec, name: &Arc<str>, def_body: &Expr) -> bool {
    let uses = |e: &Expr| expr_references(e, name) || expr_contains(e, def_body);
    if let Some(init) = &spec.init
        && uses(init)
    {
        return true;
    }
    if let Some(next) = &spec.next
        && uses(next)
    {
        return true;
    }
    if spec.invariants.iter().any(&uses) {
        return true;
    }
    if spec.liveness_properties.iter().any(|p| uses(&p.formula)) {
        return true;
    }
    if spec.safety_properties.iter().any(|p| match p {
        SafetyProperty::Init { predicate, .. } => uses(predicate),
        SafetyProperty::Action { formula, .. } => uses(formula),
    }) {
        return true;
    }
    if spec
        .quantified_fairness
        .iter()
        .any(|(_, l, r)| uses(l) || uses(r))
    {
        return true;
    }
    spec.definitions
        .iter()
        .any(|(other, (_, body))| other != name && uses(body))
}

pub fn unchecked_predicate_warning(spec: &Spec, has_count_properties: bool) -> Option<String> {
    if has_count_properties
        || !spec.liveness_properties.is_empty()
        || !spec.safety_properties.is_empty()
        || !spec.quantified_fairness.is_empty()
    {
        return None;
    }

    let candidates: Vec<&str> = spec
        .definitions
        .iter()
        .filter_map(|(name, (params, body))| {
            let body: &Expr = body;
            let looks_unchecked = params.is_empty()
                && is_boolean_shaped(body)
                && spec.vars.iter().any(|v| expr_references(body, v))
                && !crate::ast::expr_contains_temporal(body)
                && !contains_prime_ref(body, &spec.definitions)
                && spec.init.as_ref() != Some(body)
                && spec.next.as_ref() != Some(body)
                && !spec.invariant_names.iter().flatten().any(|n| n == name)
                && !predicate_is_used(spec, name, body);
            looks_unchecked.then_some(name.as_ref())
        })
        .collect();

    if candidates.is_empty() {
        return None;
    }

    Some(format!(
        "these definitions look like boolean predicates that may have been intended as invariants but are not being checked: {}. Name one with an Inv or TypeOK prefix, or list it under INVARIANT in the cfg.",
        candidates.join(", ")
    ))
}

pub fn property_violation_kind_name(kind: PropertyViolationKind) -> &'static str {
    match kind {
        PropertyViolationKind::Init => "init",
        PropertyViolationKind::Action => "action",
    }
}

pub fn check_result_to_json(result: &CheckResult, spec: &Spec) -> String {
    match result {
        CheckResult::Ok(stats) => {
            let mut parts = Vec::new();
            let status = if !stats.violations_by_invariant.is_empty() {
                "invariant_violation"
            } else if !stats.violations_by_property.is_empty() {
                "property_violation"
            } else {
                "ok"
            };
            parts.push(format!(r#""status": "{}""#, status));

            let mut stat_parts = Vec::new();
            stat_parts.push(format!(r#""states_explored": {}"#, stats.states_explored));
            stat_parts.push(format!(r#""transitions": {}"#, stats.transitions));
            stat_parts.push(format!(r#""max_depth": {}"#, stats.max_depth_reached));
            stat_parts.push(format!(r#""elapsed_secs": {:.3}"#, stats.elapsed_secs));

            if stats.violation_count > 0 {
                stat_parts.push(format!(r#""violation_count": {}"#, stats.violation_count));
                let by_inv: Vec<String> = stats
                    .violations_by_invariant
                    .iter()
                    .map(|(name, count)| {
                        let name_json = name
                            .as_ref()
                            .map(|n| json_string(n))
                            .unwrap_or_else(|| "null".to_string());
                        format!(r#"{{"name": {}, "count": {}}}"#, name_json, count)
                    })
                    .collect();
                stat_parts.push(format!(
                    r#""violations_by_invariant": [{}]"#,
                    by_inv.join(", ")
                ));
                if !stats.violations_by_property.is_empty() {
                    let by_property: Vec<String> = stats
                        .violations_by_property
                        .iter()
                        .map(|(name, count)| {
                            format!(r#"{{"name": {}, "count": {}}}"#, json_string(name), count)
                        })
                        .collect();
                    stat_parts.push(format!(
                        r#""violations_by_property": [{}]"#,
                        by_property.join(", ")
                    ));
                }
            }

            parts.push(format!(r#""stats": {{{}}}"#, stat_parts.join(", ")));

            if !stats.property_stats.is_empty() {
                let props: Vec<String> = stats
                    .property_stats
                    .iter()
                    .map(|p| {
                        let total = p.satisfied + p.violated + p.errors;
                        let ratio = if total > 0 {
                            p.satisfied as f64 / total as f64
                        } else {
                            0.0
                        };
                        let depth_entries: Vec<String> = p
                            .depth_total
                            .iter()
                            .map(|(&d, &t)| {
                                let s = p.depth_satisfied.get(&d).copied().unwrap_or(0);
                                format!(
                                    r#"{{"depth": {}, "satisfied": {}, "total": {}}}"#,
                                    d, s, t
                                )
                            })
                            .collect();
                        format!(
                            r#"{{"name": {}, "satisfied": {}, "violated": {}, "errors": {}, "total": {}, "ratio": {:.3}, "depth_breakdown": [{}]}}"#,
                            json_string(&p.name), p.satisfied, p.violated, p.errors, total, ratio, depth_entries.join(", ")
                        )
                    })
                    .collect();
                parts.push(format!(r#""properties": [{}]"#, props.join(", ")));
            }

            if !stats.properties_checked.is_empty() {
                let names: Vec<String> = stats
                    .properties_checked
                    .iter()
                    .map(|name| json_string(name))
                    .collect();
                parts.push(format!(r#""properties_checked": [{}]"#, names.join(", ")));
            }

            format!("{{{}}}", parts.join(", "))
        }
        CheckResult::InvariantViolation(cex, stats) => {
            let inv_name = spec
                .invariant_names
                .get(cex.violated_invariant)
                .and_then(|n| n.as_ref())
                .map(|n| json_string(n))
                .unwrap_or_else(|| "null".to_string());
            format!(
                r#"{{"status": "invariant_violation", "invariant_index": {}, "invariant_name": {}, "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                cex.violated_invariant,
                inv_name,
                trace_to_json_with_actions(&cex.trace, &cex.actions, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::RefinementViolation(violation, stats) => {
            let kind = if violation.at_init { "init" } else { "step" };
            format!(
                r#"{{"status": "refinement_violation", "alias": {}, "at": "{}", "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                json_string(&violation.alias),
                kind,
                trace_to_json_with_actions(&violation.trace, &violation.actions, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::PropertyViolation(violation, stats) => {
            format!(
                r#"{{"status": "property_violation", "property": {}, "kind": "{}", "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                json_string(&violation.property),
                property_violation_kind_name(violation.kind),
                trace_to_json_with_actions(&violation.trace, &violation.actions, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::Deadlock(trace, actions, stats) => {
            format!(
                r#"{{"status": "deadlock", "trace": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                trace_to_json_with_actions(trace, actions, &spec.vars),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::InitError(e) => {
            format!(
                r#"{{"status": "init_error", "error": {}}}"#,
                json_string(&format_eval_error(e))
            )
        }
        CheckResult::NextError(e, trace, _) => {
            format!(
                r#"{{"status": "next_error", "error": {}, "trace": {}}}"#,
                json_string(&format_eval_error(e)),
                trace_to_json(trace, &spec.vars)
            )
        }
        CheckResult::InvariantError(e, trace, _) => {
            format!(
                r#"{{"status": "invariant_error", "error": {}, "trace": {}}}"#,
                json_string(&format_eval_error(e)),
                trace_to_json(trace, &spec.vars)
            )
        }
        CheckResult::LivenessError(error, stats) => {
            let property = error
                .property
                .as_deref()
                .map_or("null".to_string(), json_string);
            format!(
                r#"{{"status": "liveness_error", "property": {}, "error": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                property,
                json_string(&format_eval_error(&error.error)),
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::MaxStatesExceeded(stats) => {
            format!(
                r#"{{"status": "max_states_exceeded", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::MaxDepthExceeded(stats) => {
            format!(
                r#"{{"status": "max_depth_exceeded", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::MaxTimeExceeded(stats) => {
            format!(
                r#"{{"status": "max_time_exceeded", "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                stats.states_explored,
                stats.transitions,
                stats.max_depth_reached,
                stats.elapsed_secs
            )
        }
        CheckResult::NoInitialStates => r#"{"status": "no_initial_states"}"#.to_string(),
        CheckResult::PrepareError(PrepareSpecError::InstanceError(e)) => {
            format!(
                r#"{{"status": "instance_error", "error": {}}}"#,
                json_string(&format_eval_error(e))
            )
        }
        CheckResult::PrepareError(PrepareSpecError::MissingConstants(missing)) => {
            let names: Vec<_> = missing.iter().map(|c| json_string(c)).collect();
            format!(
                r#"{{"status": "missing_constants", "constants": [{}]}}"#,
                names.join(", ")
            )
        }
        CheckResult::PrepareError(PrepareSpecError::AssumeViolation(idx)) => {
            format!(
                r#"{{"status": "assume_violation", "assume_index": {}}}"#,
                idx
            )
        }
        CheckResult::PrepareError(PrepareSpecError::AssumeError(idx, e)) => {
            format!(
                r#"{{"status": "assume_error", "assume_index": {}, "error": {}}}"#,
                idx,
                json_string(&format_eval_error(e))
            )
        }
        CheckResult::PrepareError(PrepareSpecError::NonModelValueSymmetry(name, members)) => {
            let quoted: Vec<_> = members.iter().map(|m| json_string(m)).collect();
            format!(
                r#"{{"status": "non_model_value_symmetry", "constant": {}, "members": [{}]}}"#,
                json_string(name),
                quoted.join(", ")
            )
        }
        CheckResult::PrepareError(PrepareSpecError::RefinementConfigError(message)) => {
            format!(
                r#"{{"status": "refinement_config_error", "error": {}}}"#,
                json_string(message)
            )
        }
        CheckResult::PrepareError(PrepareSpecError::LivenessProperty(message)) => {
            format!(
                r#"{{"status": "liveness_property_error", "error": {}}}"#,
                json_string(message)
            )
        }
        CheckResult::LivenessViolation(violation, stats) => {
            format!(
                r#"{{"status": "liveness_violation", "property": {}, "prefix": {}, "cycle": {}, "stats": {{"states_explored": {}, "transitions": {}, "max_depth": {}, "elapsed_secs": {:.3}}}}}"#,
                json_string(&violation.property),
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
pub fn write_trace_json(
    path: &std::path::Path,
    trace: &[State],
    vars: &[Arc<str>],
) -> std::io::Result<()> {
    use std::io::Write;
    let mut file = std::fs::File::create(path)?;
    writeln!(file, "{}", trace_to_json(trace, vars))
}

#[cfg(not(target_arch = "wasm32"))]
pub fn write_counterexample_json(
    path: &std::path::Path,
    cex: &Counterexample,
    spec_path: Option<&str>,
    vars: &[Arc<str>],
    invariant_name: Option<&str>,
) -> std::io::Result<()> {
    use std::io::Write;
    let mut file = std::fs::File::create(path)?;

    let spec_file = spec_path
        .map(json_string)
        .unwrap_or_else(|| "null".to_string());
    let inv_name = invariant_name
        .map(json_string)
        .unwrap_or_else(|| "null".to_string());
    let vars_json: Vec<String> = vars.iter().map(|v| json_string(v)).collect();

    let mut trace_entries: Vec<String> = Vec::new();
    for (i, state) in cex.trace.iter().enumerate() {
        let action = cex
            .actions
            .get(i)
            .and_then(|a| a.as_ref())
            .map(|s| json_string(s))
            .unwrap_or_else(|| "null".to_string());
        trace_entries.push(format!(
            "{{\"action\": {}, \"state\": {}}}",
            action,
            state_to_json(state, vars)
        ));
    }

    let json = format!(
        r#"{{"spec_file": {}, "invariant": {}, "violated_invariant_index": {}, "vars": [{}], "trace": [{}]}}"#,
        spec_file,
        inv_name,
        cex.violated_invariant,
        vars_json.join(", "),
        trace_entries.join(", ")
    );

    writeln!(file, "{}", json)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::ast::Expr;

    #[test]
    fn json_output_escapes_control_characters_in_errors() {
        let spec = Spec {
            vars: vec![],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: None,
            next: None,
            invariants: vec![],
            invariant_names: vec![],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };
        let result = CheckResult::InitError(EvalError::domain_error("line one\nline \"two\"\t"));
        let json = check_result_to_json(&result, &spec);
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
        assert!(
            parsed["error"]
                .as_str()
                .is_some_and(|e| e.contains("line one\nline \"two\""))
        );
    }

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

    fn labeled_action(name: &str, e: Expr) -> Expr {
        Expr::LabeledAction(var(name), Box::new(e))
    }

    fn fn_call0(name: &str) -> Expr {
        Expr::FnCall(var(name), vec![])
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
            init: Some(eq(var_expr("count"), lit_int(0))),
            next: Some(and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            )),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
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
    fn json_status_reflects_violations_under_continue() {
        let spec = Spec {
            vars: vec![var("count")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: Some(eq(var_expr("count"), lit_int(0))),
            next: Some(and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            )),
            invariants: vec![le(var_expr("count"), lit_int(1))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig {
            allow_deadlock: true,
            continue_on_violation: true,
            ..CheckerConfig::default()
        };
        let result = check(&spec, &domains, &config);

        match &result {
            CheckResult::Ok(stats) => assert!(stats.violation_count > 0),
            other => panic!("expected Ok with recorded violations, got {:?}", other),
        }

        let json = check_result_to_json(&result, &spec);
        assert!(
            json.contains(r#""status": "invariant_violation""#),
            "status must reflect the recorded violations, got: {json}"
        );
    }

    fn spec_with(invariants: Vec<Expr>) -> Spec {
        let init = eq(var_expr("x"), lit_int(0));
        let safety = le(var_expr("x"), lit_int(1));
        let mut definitions = BTreeMap::new();
        definitions.insert(var("Init"), (vec![], Arc::new(init.clone())));
        definitions.insert(var("Safety"), (vec![], Arc::new(safety)));
        let invariant_names = invariants.iter().map(|_| None).collect();
        Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions,
            assumes: vec![],
            instances: vec![],
            init: Some(init),
            next: None,
            invariants,
            invariant_names,
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        }
    }

    #[test]
    fn warns_for_boolean_def_when_nothing_checked() {
        let msg = unchecked_predicate_warning(&spec_with(vec![]), false)
            .expect("should warn when nothing is checked");
        assert!(msg.contains("Safety"), "got: {msg}");
        assert!(!msg.contains("Init"), "init must be excluded: {msg}");
    }

    #[test]
    fn no_warning_when_an_invariant_is_present() {
        let spec = spec_with(vec![le(var_expr("x"), lit_int(1))]);
        assert!(unchecked_predicate_warning(&spec, false).is_none());
    }

    #[test]
    fn no_warning_when_count_properties_present() {
        assert!(unchecked_predicate_warning(&spec_with(vec![]), true).is_none());
    }

    #[test]
    fn warns_for_misnamed_invariant_even_when_another_is_checked() {
        let spec = spec_with(vec![le(var_expr("x"), lit_int(3))]);
        let msg = unchecked_predicate_warning(&spec, false)
            .expect("a dangling misnamed invariant should warn even alongside a checked one");
        assert!(msg.contains("Safety"), "got: {msg}");
    }

    #[test]
    fn no_warning_for_helper_predicate_inlined_into_next() {
        let init = eq(var_expr("x"), lit_int(0));
        let guard = lt(var_expr("x"), lit_int(5));
        let next = and(
            eq(prime_expr("x"), add(var_expr("x"), lit_int(1))),
            guard.clone(),
        );
        let mut definitions = BTreeMap::new();
        definitions.insert(var("Init"), (vec![], Arc::new(init.clone())));
        definitions.insert(var("Next"), (vec![], Arc::new(next.clone())));
        definitions.insert(var("Guard"), (vec![], Arc::new(guard)));
        let spec = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions,
            assumes: vec![],
            instances: vec![],
            init: Some(init),
            next: Some(next),
            invariants: vec![le(var_expr("x"), lit_int(10))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };
        assert!(
            unchecked_predicate_warning(&spec, false).is_none(),
            "an inlined helper predicate must not be flagged as an unchecked invariant"
        );
    }

    #[test]
    fn no_warning_for_temporal_spec_formula() {
        let init = eq(var_expr("x"), lit_int(0));
        let next = eq(prime_expr("x"), add(var_expr("x"), lit_int(1)));
        let temporal = and(
            init.clone(),
            Expr::BoxAction(Box::new(next.clone()), Box::new(Expr::Var(var("x")))),
        );
        let mut definitions = BTreeMap::new();
        definitions.insert(var("Init"), (vec![], Arc::new(init.clone())));
        definitions.insert(var("Next"), (vec![], Arc::new(next.clone())));
        definitions.insert(var("Spec"), (vec![], Arc::new(temporal)));
        let spec = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions,
            assumes: vec![],
            instances: vec![],
            init: Some(init),
            next: Some(next),
            invariants: vec![le(var_expr("x"), lit_int(10))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };
        assert!(
            unchecked_predicate_warning(&spec, false).is_none(),
            "a temporal specification formula must not be flagged as an unchecked invariant"
        );
    }

    #[test]
    fn export_dot_string_produces_graph() {
        let spec = Spec {
            vars: vec![var("count")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: Some(eq(var_expr("count"), lit_int(0))),
            next: Some(and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(2))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            )),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig {
            allow_deadlock: true,
            export_dot_string: true,
            ..CheckerConfig::default()
        };
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::Ok(stats) => {
                let dot = stats.dot_graph.expect("dot_graph should be Some");
                assert!(dot.contains("digraph StateGraph"));
                assert!(dot.contains("s0"));
                assert!(dot.contains("s0 -> s1"));
            }
            other => panic!("expected Ok, got {:?}", other),
        }
    }

    #[test]
    fn export_dot_includes_back_edges() {
        let spec = Spec {
            vars: vec![var("count")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::new(),
            assumes: vec![],
            instances: vec![],
            init: Some(eq(var_expr("count"), lit_int(0))),
            next: Some(eq(
                prime_expr("count"),
                Expr::Mod(
                    Box::new(add(var_expr("count"), lit_int(1))),
                    Box::new(lit_int(3)),
                ),
            )),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig {
            allow_deadlock: true,
            export_dot_string: true,
            ..CheckerConfig::default()
        };
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::Ok(stats) => {
                assert_eq!(stats.states_explored, 3);
                let dot = stats.dot_graph.expect("dot_graph should be Some");
                assert!(dot.contains("s0 -> s1"), "missing edge 0→1");
                assert!(dot.contains("s1 -> s2"), "missing edge 1→2");
                assert!(dot.contains("s2 -> s0"), "missing back-edge 2→0");
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
            init: Some(eq(var_expr("count"), lit_int(0))),
            next: Some(and(
                in_set(var_expr("count"), set_range(lit_int(0), lit_int(4))),
                eq(prime_expr("count"), add(var_expr("count"), lit_int(1))),
            )),
            invariants: vec![le(var_expr("count"), lit_int(3))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let domains = Env::new();
        let config = CheckerConfig::default();
        let result = check(&spec, &domains, &config);

        match result {
            CheckResult::InvariantViolation(cex, _stats) => {
                assert_eq!(cex.violated_invariant, 0);
                assert_eq!(cex.trace.len(), 5);
                let final_state = cex.trace.last().unwrap();
                assert_eq!(final_state.values.first(), Some(&Value::Int(4)));
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
            init: Some(and(
                eq(var_expr("lo"), lit_int(0)),
                eq(var_expr("hi"), lit_int(0)),
            )),
            next: Some(or(
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
            )),
            invariants: vec![
                le(var_expr("lo"), lit_int(1)),
                le(var_expr("hi"), lit_int(1)),
            ],
            invariant_names: vec![None, None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
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
            init: Some(eq(var_expr("x"), lit_int(0))),
            next: Some(and(
                eq(var_expr("x"), lit_int(99)),
                eq(prime_expr("x"), lit_int(100)),
            )),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
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
            init: Some(eq(var_expr("x"), lit_int(0))),
            next: Some(and(
                lt(var_expr("x"), lit_int(2)),
                eq(prime_expr("x"), add(var_expr("x"), lit_int(1))),
            )),
            invariants: vec![lit_bool(true)],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let result = check(&spec, &Env::new(), &CheckerConfig::default());
        match result {
            CheckResult::Deadlock(trace, _, _) => {
                assert_eq!(trace.len(), 3);
                let final_state = trace.last().unwrap();
                assert_eq!(final_state.values.first(), Some(&Value::Int(2)));
            }
            other => panic!("expected Deadlock, got {:?}", other),
        }
    }

    #[test]
    fn format_trace_output() {
        let state = State {
            values: vec![
                Value::Int(42),
                Value::set([Value::Int(1), Value::Int(2)].into()),
            ],
        };

        let trace = vec![state];
        let vars = vec![var("x"), var("y")];
        let output = format_trace(&trace, &vars);

        assert!(output.contains("State 0"));
        assert!(output.contains("x = 42"));
        assert!(output.contains("y = {1, 2}"));
    }

    #[test]
    fn counterexample_actions_alignment() {
        // Case 1: Violation in initial state
        // Init == x = 1
        // Action == x' = x
        // Next == Action
        // Invariant == x < 1
        let spec1 = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::from([(
                Arc::from("Action"),
                (vec![], Arc::new(eq(prime_expr("x"), var_expr("x")))),
            )]),
            assumes: vec![],
            instances: vec![],
            init: Some(eq(var_expr("x"), lit_int(1))),
            next: Some(labeled_action("Action", fn_call0("Action"))),
            invariants: vec![lt(var_expr("x"), lit_int(1))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let result1 = check(&spec1, &Env::new(), &CheckerConfig::default());
        match result1 {
            CheckResult::InvariantViolation(cex, _) => {
                assert_eq!(cex.trace.len(), 1);
                assert_eq!(cex.actions.len(), 1);
                assert_eq!(cex.actions[0], None);
                assert_eq!(cex.trace[0].values[0], Value::Int(1));
            }
            res => panic!(
                "Expected invariant violation in initial state, got {:?}",
                res
            ),
        }

        // Case 2: Violation in second state
        // Init: x = 0
        // Action == x = 0 /\ x' = 1
        // Next == Action
        // Invariant == x < 1
        let spec2 = Spec {
            vars: vec![var("x")],
            constants: vec![],
            extends: vec![],
            definitions: BTreeMap::from([(
                Arc::from("Action"),
                (
                    vec![],
                    Arc::new(and(
                        eq(var_expr("x"), lit_int(0)),
                        eq(prime_expr("x"), lit_int(1)),
                    )),
                ),
            )]),
            assumes: vec![],
            instances: vec![],
            init: Some(eq(var_expr("x"), lit_int(0))),
            next: Some(labeled_action("Action", fn_call0("Action"))),
            invariants: vec![lt(var_expr("x"), lit_int(1))],
            invariant_names: vec![None],
            fairness: vec![],
            quantified_fairness: vec![],
            liveness_properties: vec![],
            safety_properties: vec![],
            temporal_assumptions: vec![],
        };

        let result2 = check(&spec2, &Env::new(), &CheckerConfig::default());
        match result2 {
            CheckResult::InvariantViolation(cex, _) => {
                assert_eq!(cex.trace.len(), 2);
                assert_eq!(cex.actions.len(), 2);
                assert_eq!(cex.actions[0], None);
                assert_eq!(cex.actions[1], Some(Arc::from("Action")));
                assert_eq!(cex.trace[0].values[0], Value::Int(0));
                assert_eq!(cex.trace[1].values[0], Value::Int(1));
            }
            res => panic!(
                "Expected invariant violation in second state, got {:?}",
                res
            ),
        }
    }
}
