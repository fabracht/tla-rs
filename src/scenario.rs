use std::sync::Arc;

use crate::ast::{Env, Expr, Spec, State, Transition, Value};
use crate::checker::format_value;
use crate::eval::{Definitions, EvalError, make_primed_names, next_states};
use crate::parser::parse_expr;

#[derive(Debug, Clone)]
pub enum ScenarioStep {
    Condition(Expr),
}

#[derive(Debug, Clone)]
pub struct Scenario {
    pub steps: Vec<ScenarioStep>,
}

#[derive(Debug)]
pub struct ScenarioResult {
    pub states: Vec<(ScenarioStep, State, Vec<String>)>,
    pub failure: Option<ScenarioFailure>,
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

        if let Some(expr_text) = line.strip_prefix("step:") {
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
                "line {}: expected 'step: <expression>', found '{}'",
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
    let mut env = constants.clone();

    let init_states = crate::eval::init_states(&spec.init, &spec.vars, &env, &defs)?;
    let Some(mut current_state) = init_states.into_iter().next() else {
        return Err(EvalError::domain_error("no initial states"));
    };
    let mut results: Vec<(ScenarioStep, State, Vec<String>)> = Vec::new();
    let primed_vars = make_primed_names(&spec.vars);

    results.push((
        ScenarioStep::Condition(Expr::Lit(Value::Bool(true))),
        current_state.clone(),
        vec!["Initial state".to_string()],
    ));

    for (step_idx, step) in scenario.steps.iter().enumerate() {
        for (i, var) in spec.vars.iter().enumerate() {
            if let Some(val) = current_state.values.get(i) {
                env.insert(var.clone(), val.clone());
            }
        }

        let successors = next_states(
            &spec.next,
            &current_state,
            &spec.vars,
            &primed_vars,
            &mut env,
            &defs,
        )?;

        let matching =
            find_matching_transition(&successors, step, &current_state, &defs, &spec.vars)?;

        match matching {
            Some((transition, changes)) => {
                current_state = transition.state.clone();
                results.push((step.clone(), transition.state, changes));
            }
            None => {
                let available = describe_available_actions(&successors, &current_state, &spec.vars);
                return Ok(ScenarioResult {
                    states: results,
                    failure: Some(ScenarioFailure {
                        step_index: step_idx,
                        step: step.clone(),
                        message: "no transition matches condition".to_string(),
                        available_actions: available,
                    }),
                });
            }
        }
    }

    Ok(ScenarioResult {
        states: results,
        failure: None,
    })
}

fn build_definitions(spec: &Spec) -> Definitions {
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
            let primed_name: Arc<str> = format!("{}'", var).into();
            env.insert(primed_name, val.clone());
        }
    }
    env
}

fn find_matching_transition(
    successors: &[Transition],
    step: &ScenarioStep,
    current: &State,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Option<(Transition, Vec<String>)>, EvalError> {
    for transition in successors {
        if matches_step(current, &transition.state, step, defs, vars)? {
            let changes = compute_changes(current, &transition.state, vars);
            return Ok(Some((transition.clone(), changes)));
        }
    }
    Ok(None)
}

fn matches_step(
    current: &State,
    next: &State,
    step: &ScenarioStep,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<bool, EvalError> {
    match step {
        ScenarioStep::Condition(expr) => {
            let mut env = build_scenario_env(current, next, &Env::new(), vars);
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
    }
}

fn compute_changes(current: &State, next: &State, vars: &[Arc<str>]) -> Vec<String> {
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
}
