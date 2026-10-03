use std::collections::HashSet;
use std::sync::Arc;

use crate::ast::{Env, Expr, Spec, State, Transition, Value};
use crate::checker::format_value;
use crate::eval::{Definitions, EvalError, make_primed_names, next_states};
use crate::parser::parse_expr;

#[derive(Debug, Clone)]
pub enum ScenarioStep {
    Condition(Expr),
    Action {
        name: Arc<str>,
        condition: Option<Expr>,
    },
}

#[derive(Debug, Clone)]
pub struct Scenario {
    pub steps: Vec<ScenarioStep>,
}

#[derive(Debug)]
pub struct ScenarioResult {
    pub states: Vec<(ScenarioStep, State, Vec<String>)>,
    pub failure: Option<ScenarioFailure>,
    /// How many unobserved transitions the replay had to take to line the
    /// scenario up with the spec, within the allowed stutter budget.
    pub stutters: usize,
    /// Which initial state the replay started from, and how many `Init`
    /// admits. A spec with several initial states is replayed from each in
    /// turn until one admits the whole scenario.
    pub init_index: usize,
    pub init_count: usize,
}

#[derive(Debug)]
pub struct ScenarioFailure {
    pub step_index: usize,
    pub step: ScenarioStep,
    pub message: String,
    pub available_actions: Vec<String>,
}

pub fn parse_scenario(input: &str) -> Result<Scenario, String> {
    let mut steps = Vec::new();

    for (line_num, line) in input.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if let Some(rest) = line.strip_prefix("action:") {
            let rest = rest.trim();
            let (name_part, cond_part) = match rest.split_once(';') {
                Some((name, cond)) => (name.trim(), Some(cond.trim())),
                None => (rest, None),
            };
            if name_part.is_empty() {
                return Err(format!(
                    "line {}: 'action:' requires an action name",
                    line_num + 1
                ));
            }
            let condition = match cond_part {
                Some(cond) if !cond.is_empty() => match parse_expr(cond) {
                    Ok(expr) => Some(expr),
                    Err(e) => {
                        return Err(format!(
                            "line {}: failed to parse condition '{}': {}",
                            line_num + 1,
                            cond,
                            e.message
                        ));
                    }
                },
                _ => None,
            };
            steps.push(ScenarioStep::Action {
                name: name_part.into(),
                condition,
            });
        } else if let Some(expr_text) = line.strip_prefix("step:") {
            let expr_text = expr_text.trim();
            match parse_expr(expr_text) {
                Ok(expr) => steps.push(ScenarioStep::Condition(expr)),
                Err(e) => {
                    return Err(format!(
                        "line {}: failed to parse expression '{}': {}",
                        line_num + 1,
                        expr_text,
                        e.message
                    ));
                }
            }
        } else {
            return Err(format!(
                "line {}: expected 'step: <expression>' or 'action: <Name>', found '{}'",
                line_num + 1,
                line
            ));
        }
    }

    Ok(Scenario { steps })
}

pub fn execute_scenario(
    spec: &Spec,
    scenario: &Scenario,
    constants: &Env,
) -> Result<ScenarioResult, EvalError> {
    let defs = build_definitions(spec);
    execute_scenario_with(spec, scenario, constants, &defs)
}

/// Replay a scenario that records only some of the system's steps: between two
/// recorded steps the spec may take up to `max_stutter` transitions of its own.
/// A trace collected from a running program needs this, because instrumentation
/// never sees every step the spec models.
pub fn execute_scenario_stuttering(
    spec: &Spec,
    scenario: &Scenario,
    constants: &Env,
    defs: &Definitions,
    max_stutter: usize,
) -> Result<ScenarioResult, EvalError> {
    replay(spec, scenario, constants, defs, max_stutter)
}

pub fn execute_scenario_with(
    spec: &Spec,
    scenario: &Scenario,
    constants: &Env,
    defs: &Definitions,
) -> Result<ScenarioResult, EvalError> {
    replay(spec, scenario, constants, defs, 0)
}

fn replay(
    spec: &Spec,
    scenario: &Scenario,
    constants: &Env,
    defs: &Definitions,
    max_stutter: usize,
) -> Result<ScenarioResult, EvalError> {
    let mut bound_constants = constants.clone();
    crate::config::bind_model_value_names(&mut bound_constants, spec, defs);
    let constants = &bound_constants;
    let mut env = constants.clone();

    let init_expr = spec
        .init
        .as_ref()
        .ok_or_else(|| EvalError::domain_error("scenario mode requires Init definition"))?;
    let next_expr = spec
        .next
        .as_ref()
        .ok_or_else(|| EvalError::domain_error("scenario mode requires Next definition"))?;
    let init_states = crate::eval::init_states(init_expr, &spec.vars, &env, defs)?;
    let init_count = init_states.len();
    if init_count == 0 {
        return Err(EvalError::domain_error("no initial states"));
    }
    let replay = Replay {
        spec,
        scenario,
        next_expr,
        constants,
        defs,
        init_count,
        max_stutter,
    };
    let mut first_outcome: Option<ScenarioResult> = None;
    for (init_index, initial) in init_states.into_iter().enumerate() {
        let outcome = replay.from(initial, init_index, &mut env)?;
        if outcome.failure.is_none() {
            return Ok(outcome);
        }
        first_outcome.get_or_insert(outcome);
    }
    first_outcome.ok_or_else(|| EvalError::domain_error("no initial states"))
}

/// One scenario replayed against one spec: everything except which initial
/// state the attempt starts from.
struct Replay<'a> {
    spec: &'a Spec,
    scenario: &'a Scenario,
    next_expr: &'a Expr,
    constants: &'a Env,
    defs: &'a Definitions,
    init_count: usize,
    max_stutter: usize,
}

impl Replay<'_> {
    fn from(
        &self,
        initial: State,
        init_index: usize,
        env: &mut Env,
    ) -> Result<ScenarioResult, EvalError> {
        let Replay {
            spec,
            scenario,
            next_expr,
            constants,
            defs,
            init_count,
            max_stutter,
        } = *self;
        let mut current_state = initial;
        let mut stutters = 0;
        let mut results: Vec<(ScenarioStep, State, Vec<String>)> = Vec::new();
        let primed_vars = make_primed_names(&spec.vars);
        let search = Search {
            next_expr,
            vars: &spec.vars,
            primed_vars: &primed_vars,
            constants,
            defs,
            max_stutter,
        };

        results.push((
            ScenarioStep::Condition(Expr::Lit(Value::Bool(true))),
            current_state.clone(),
            vec!["Initial state".to_string()],
        ));

        for (step_idx, step) in scenario.steps.iter().enumerate() {
            match search.reach(&current_state, step, env)? {
                Some(path) => {
                    stutters += path.unobserved.len();
                    for (state, changes) in path.unobserved {
                        results.push((unobserved_step(), state, changes));
                    }
                    current_state = path.state.clone();
                    results.push((step.clone(), path.state, path.changes));
                }
                None => {
                    let successors = next_states(
                        next_expr,
                        &current_state,
                        &spec.vars,
                        &primed_vars,
                        env,
                        defs,
                    )?;
                    let available =
                        describe_available_actions(&successors, &current_state, &spec.vars);
                    return Ok(ScenarioResult {
                        states: results,
                        failure: Some(ScenarioFailure {
                            step_index: step_idx,
                            step: step.clone(),
                            message: match (init_count, max_stutter) {
                                (1, 0) => "no transition matches condition".to_string(),
                                (1, n) => format!(
                                    "no transition matches condition within {n} unobserved steps"
                                ),
                                (n, 0) => format!(
                                    "no transition matches condition (from initial state {} of {n})",
                                    init_index + 1
                                ),
                                (n, stutter) => format!(
                                    "no transition matches condition within {stutter} unobserved steps (from initial state {} of {n})",
                                    init_index + 1
                                ),
                            },
                            available_actions: available,
                        }),
                        init_index,
                        init_count,
                        stutters,
                    });
                }
            }
        }

        Ok(ScenarioResult {
            states: results,
            failure: None,
            init_index,
            init_count,
            stutters,
        })
    }
}

fn unobserved_step() -> ScenarioStep {
    ScenarioStep::Condition(Expr::Lit(Value::Bool(true)))
}

/// A spec transition the scenario did not record, plus the recorded step it
/// made reachable.
struct StutterPath {
    unobserved: Vec<(State, Vec<String>)>,
    state: State,
    changes: Vec<String>,
}

/// Breadth-first search for the recorded step, allowing the spec to take up to
/// `max_stutter` unobserved transitions before it.
struct Search<'a> {
    next_expr: &'a Expr,
    vars: &'a [Arc<str>],
    primed_vars: &'a [Arc<str>],
    constants: &'a Env,
    defs: &'a Definitions,
    max_stutter: usize,
}

impl Search<'_> {
    fn reach(
        &self,
        start: &State,
        step: &ScenarioStep,
        env: &mut Env,
    ) -> Result<Option<StutterPath>, EvalError> {
        let mut frontier = vec![(start.clone(), Vec::new())];
        let mut seen = HashSet::from([start.clone()]);

        for depth in 0..=self.max_stutter {
            let mut next_frontier = Vec::new();
            for (state, unobserved) in frontier {
                let successors = next_states(
                    self.next_expr,
                    &state,
                    self.vars,
                    self.primed_vars,
                    env,
                    self.defs,
                )?;
                if let Some((transition, changes)) = find_matching_transition(
                    &successors,
                    step,
                    &state,
                    self.constants,
                    self.defs,
                    self.vars,
                )? {
                    return Ok(Some(StutterPath {
                        unobserved,
                        state: transition.state,
                        changes,
                    }));
                }
                if depth == self.max_stutter {
                    continue;
                }
                for transition in successors {
                    if !seen.insert(transition.state.clone()) {
                        continue;
                    }
                    let changes = compute_changes(&state, &transition.state, self.vars);
                    let mut path = unobserved.clone();
                    path.push((transition.state.clone(), changes));
                    next_frontier.push((transition.state, path));
                }
            }
            frontier = next_frontier;
        }
        Ok(None)
    }
}

/// The definition table a scenario is evaluated against: the spec's own
/// definitions. Public so embedders can reuse it with
/// [`execute_scenario_with`] instead of rebuilding it.
pub fn build_definitions(spec: &Spec) -> Definitions {
    let mut defs = Definitions::new();
    for (name, (params, body)) in &spec.definitions {
        defs.insert(name.clone(), (params.clone(), body.clone()));
    }
    defs
}

fn build_scenario_env(current: &State, next: &State, constants: &Env, vars: &[Arc<str>]) -> Env {
    let mut env = constants.clone();
    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = current.values.get(i) {
            env.insert(var.clone(), val.clone());
        }
        if let Some(val) = next.values.get(i) {
            let primed_name = crate::intern::primed_name(var);
            env.insert(primed_name, val.clone());
        }
    }
    env
}

fn find_matching_transition(
    successors: &[Transition],
    step: &ScenarioStep,
    current: &State,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Option<(Transition, Vec<String>)>, EvalError> {
    for transition in successors {
        if matches_step(current, transition, step, constants, defs, vars)? {
            let changes = compute_changes(current, &transition.state, vars);
            return Ok(Some((transition.clone(), changes)));
        }
    }
    Ok(None)
}

fn matches_step(
    current: &State,
    transition: &Transition,
    step: &ScenarioStep,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<bool, EvalError> {
    match step {
        ScenarioStep::Condition(expr) => {
            eval_condition(current, &transition.state, expr, constants, defs, vars)
        }
        ScenarioStep::Action { name, condition } => {
            if transition.action.as_deref() != Some(name.as_ref()) {
                return Ok(false);
            }
            match condition {
                Some(expr) => {
                    eval_condition(current, &transition.state, expr, constants, defs, vars)
                }
                None => Ok(true),
            }
        }
    }
}

fn eval_condition(
    current: &State,
    next: &State,
    expr: &Expr,
    constants: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<bool, EvalError> {
    let mut env = build_scenario_env(current, next, constants, vars);
    match crate::eval::eval(expr, &mut env, defs) {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(other) => Err(EvalError::TypeMismatch {
            expected: "Bool",
            got: other,
            context: Some("scenario condition"),
            span: None,
        }),
        Err(e) => Err(e),
    }
}

pub(crate) fn compute_changes(current: &State, next: &State, vars: &[Arc<str>]) -> Vec<String> {
    let mut changes = Vec::new();

    for (i, var) in vars.iter().enumerate() {
        let next_val = next.values.get(i);
        let curr_val = current.values.get(i);
        match (curr_val, next_val) {
            (Some(cv), Some(nv)) if cv != nv => {
                changes.push(format!(
                    "{}: {} → {}",
                    var,
                    format_value_compact(cv),
                    format_value_compact(nv)
                ));
            }
            (None, Some(nv)) => {
                changes.push(format!("{}: (new) {}", var, format_value_compact(nv)));
            }
            _ => {}
        }
    }

    changes
}

fn format_value_compact(v: &Value) -> String {
    match v {
        Value::Bool(b) => b.to_string(),
        Value::Int(n) => n.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Model(m) => m.to_string(),
        Value::IntSet(d) => d.name().to_string(),
        Value::Set(s) if s.is_empty() => "{}".to_string(),
        Value::Set(s) => {
            let items: Vec<String> = s.iter().take(3).map(format_value_compact).collect();
            if s.len() > 3 {
                format!("{{{}, ...}}", items.join(", "))
            } else {
                format!("{{{}}}", items.join(", "))
            }
        }
        Value::Tuple(t) if t.is_empty() => "<<>>".to_string(),
        Value::Tuple(t) => {
            let items: Vec<String> = t.iter().take(3).map(format_value_compact).collect();
            if t.len() > 3 {
                format!("<<{}, ...>>", items.join(", "))
            } else {
                format!("<<{}>>", items.join(", "))
            }
        }
        Value::Fn(f) => {
            let items: Vec<String> = f
                .iter()
                .take(2)
                .map(|(k, v)| format!("{} ↦ {}", format_value_compact(k), format_value_compact(v)))
                .collect();
            if f.len() > 2 {
                format!("[{}, ...]", items.join(", "))
            } else {
                format!("[{}]", items.join(", "))
            }
        }
        Value::Record(r) => {
            let items: Vec<String> = r
                .iter()
                .take(2)
                .map(|(k, v)| format!("{}: {}", k, format_value_compact(v)))
                .collect();
            if r.len() > 2 {
                format!("[{}, ...]", items.join(", "))
            } else {
                format!("[{}]", items.join(", "))
            }
        }
    }
}

fn describe_available_actions(
    successors: &[Transition],
    current: &State,
    vars: &[Arc<str>],
) -> Vec<String> {
    let mut actions = Vec::new();

    for transition in successors {
        let changes = compute_changes(current, &transition.state, vars);
        let action_name = transition
            .action
            .as_ref()
            .map(|s| s.as_ref())
            .unwrap_or("(unnamed)");
        if !changes.is_empty() {
            let summary = if changes.len() > 2 {
                format!(
                    "{}: {}, ... ({} changes)",
                    action_name,
                    changes[..2].join("; "),
                    changes.len()
                )
            } else {
                format!("{}: {}", action_name, changes.join("; "))
            };
            actions.push(summary);
        } else {
            actions.push(format!("{}: (no changes)", action_name));
        }
    }

    actions.truncate(10);
    actions
}

fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Lit(Value::Bool(true)) => "TRUE".to_string(),
        Expr::Lit(Value::Bool(false)) => "FALSE".to_string(),
        Expr::Lit(Value::Int(n)) => n.to_string(),
        Expr::Lit(Value::Str(s)) => format!("\"{}\"", s),
        Expr::Var(name) => name.to_string(),
        Expr::Prime(name) => format!("{}'", name),
        Expr::Eq(l, r) => format!("{} = {}", format_expr(l), format_expr(r)),
        Expr::In(l, r) => format!("{} \\in {}", format_expr(l), format_expr(r)),
        Expr::And(l, r) => format!("{} /\\ {}", format_expr(l), format_expr(r)),
        Expr::Or(l, r) => format!("{} \\/ {}", format_expr(l), format_expr(r)),
        Expr::Neq(l, r) => format!("{} # {}", format_expr(l), format_expr(r)),
        Expr::Gt(l, r) => format!("{} > {}", format_expr(l), format_expr(r)),
        Expr::Lt(l, r) => format!("{} < {}", format_expr(l), format_expr(r)),
        Expr::FnApp(f, arg) => format!("{}[{}]", format_expr(f), format_expr(arg)),
        _ => format!("{:?}", expr),
    }
}

pub fn format_scenario_result(
    result: &ScenarioResult,
    vars_of_interest: &[&str],
    spec_vars: &[Arc<str>],
) -> String {
    let mut output = String::new();

    for (idx, (step, state, changes)) in result.states.iter().enumerate() {
        output.push_str(&format!("\n━━━ Step {} ━━━\n", idx));

        match step {
            ScenarioStep::Condition(expr) => {
                if idx == 0 {
                    output.push_str("Action: Init\n");
                } else {
                    output.push_str(&format!("Condition: {}\n", format_expr(expr)));
                }
            }
            ScenarioStep::Action { name, condition } => match condition {
                Some(expr) => {
                    output.push_str(&format!("Action: {} where {}\n", name, format_expr(expr)));
                }
                None => output.push_str(&format!("Action: {}\n", name)),
            },
        }

        if !changes.is_empty() && idx > 0 {
            output.push_str("Changes:\n");
            for change in changes {
                output.push_str(&format!("  • {}\n", change));
            }
        }

        if !vars_of_interest.is_empty() {
            output.push_str("State:\n");
            for var in vars_of_interest {
                if let Some(vi) = spec_vars.iter().position(|v| v.as_ref() == *var)
                    && let Some(val) = state.values.get(vi)
                {
                    output.push_str(&format!("  {} = {}\n", var, format_value(val)));
                }
            }
        }
    }

    if let Some(failure) = &result.failure {
        output.push_str(&format!(
            "\n⚠ Scenario failed at step {}\n",
            failure.step_index + 1
        ));
        match &failure.step {
            ScenarioStep::Condition(expr) => {
                output.push_str(&format!("  Condition: {}\n", format_expr(expr)));
            }
            ScenarioStep::Action { name, condition } => match condition {
                Some(expr) => {
                    output.push_str(&format!("  Action: {} where {}\n", name, format_expr(expr)));
                }
                None => output.push_str(&format!("  Action: {}\n", name)),
            },
        }
        output.push_str(&format!("  Reason: {}\n", failure.message));

        if !failure.available_actions.is_empty() {
            output.push_str("\n  Available transitions:\n");
            for (i, action) in failure.available_actions.iter().enumerate() {
                output.push_str(&format!("    {}. {}\n", i + 1, action));
            }
        }
    } else {
        output.push_str("\n✓ Scenario completed successfully\n");
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_condition() {
        let input = r#"
            step: x' > x
        "#;

        let scenario = parse_scenario(input).unwrap();
        assert_eq!(scenario.steps.len(), 1);
    }

    #[test]
    fn parse_multiple_conditions() {
        let input = r#"
            # First step
            step: x' = 1
            # Second step
            step: x' = 2
        "#;

        let scenario = parse_scenario(input).unwrap();
        assert_eq!(scenario.steps.len(), 2);
    }

    #[test]
    fn parse_complex_condition() {
        let input = r#"step: "s1" \in active' /\ "s1" \notin active"#;

        let scenario = parse_scenario(input).unwrap();
        assert_eq!(scenario.steps.len(), 1);
    }

    #[test]
    fn parse_fn_app_condition() {
        let input = r#"step: pc'["p1"] = "critical""#;

        let scenario = parse_scenario(input).unwrap();
        assert_eq!(scenario.steps.len(), 1);
    }

    #[test]
    fn reject_invalid_line() {
        let input = "s1: activate";
        let result = parse_scenario(input);
        assert!(result.is_err());
    }

    #[test]
    fn parse_action_step() {
        let scenario = parse_scenario("action: NTPSync").unwrap();
        assert_eq!(scenario.steps.len(), 1);
        match &scenario.steps[0] {
            ScenarioStep::Action { name, condition } => {
                assert_eq!(name.as_ref(), "NTPSync");
                assert!(condition.is_none());
            }
            _ => panic!("expected action step"),
        }
    }

    #[test]
    fn parse_action_step_with_condition() {
        let scenario = parse_scenario("action: Inc; x' > x").unwrap();
        match &scenario.steps[0] {
            ScenarioStep::Action { name, condition } => {
                assert_eq!(name.as_ref(), "Inc");
                assert!(condition.is_some());
            }
            _ => panic!("expected action step"),
        }
    }

    #[test]
    fn reject_empty_action() {
        assert!(parse_scenario("action:").is_err());
    }

    fn inc_dec_spec() -> (Spec, Env) {
        let src = r#"---- MODULE T ----
EXTENDS Integers
CONSTANT N
VARIABLES x
Init == x = 0
Inc == x' = x + 1
Dec == x' = x - 1
Next == Inc \/ Dec
===="#;
        let spec = crate::parser::parse(src).expect("spec parses");
        let mut domains = Env::new();
        domains.insert("N".into(), Value::Int(3));
        (spec, domains)
    }

    #[test]
    fn constant_resolves_in_step_predicate() {
        let (spec, domains) = inc_dec_spec();
        let scenario = parse_scenario("step: x' = x + 1 /\\ N = 3").unwrap();
        let result = execute_scenario(&spec, &scenario, &domains).expect("constant should resolve");
        assert!(result.failure.is_none());
        assert_eq!(result.states.len(), 2);
    }

    #[test]
    fn action_pins_named_transition() {
        let (spec, domains) = inc_dec_spec();
        let scenario = parse_scenario("action: Dec").unwrap();
        let result = execute_scenario(&spec, &scenario, &domains).unwrap();
        assert!(result.failure.is_none());
        assert_eq!(
            result.states.last().unwrap().1.values.first(),
            Some(&Value::Int(-1))
        );
    }

    #[test]
    fn unknown_action_fails_without_match() {
        let (spec, domains) = inc_dec_spec();
        let scenario = parse_scenario("action: Nope").unwrap();
        let result = execute_scenario(&spec, &scenario, &domains).unwrap();
        assert!(result.failure.is_some());
    }

    #[test]
    fn action_pins_top_level_existential() {
        let src = r#"---- MODULE T ----
EXTENDS Integers
VARIABLES y, z
Init == y = 0 /\ z = 0
ConjAction == y' = 1 /\ z' = 0
TopExists == \E q \in 1..3 : y' = q /\ z' = 1
Next == ConjAction \/ TopExists
===="#;
        let spec = crate::parser::parse(src).expect("spec parses");
        let domains = Env::new();
        let scenario = parse_scenario("action: TopExists; y' = 2").unwrap();
        let result = execute_scenario(&spec, &scenario, &domains).unwrap();
        assert!(
            result.failure.is_none(),
            "an action whose body is a top-level existential must be pinnable by name"
        );
        assert_eq!(
            result.states.last().unwrap().1.values,
            vec![Value::Int(2), Value::Int(1)]
        );
    }
}
