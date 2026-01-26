use std::sync::Arc;

use crate::ast::{Env, Expr, Spec, State, Value};
use crate::checker::format_value;
use crate::eval::{next_states, Definitions, EvalError};
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
                    ))
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
    if init_states.is_empty() {
        return Err(EvalError::DomainError("no initial states".into()));
    }

    let mut current_state = init_states.into_iter().next().unwrap();
    let mut results: Vec<(ScenarioStep, State, Vec<String>)> = Vec::new();

    results.push((
        ScenarioStep::Condition(Expr::Lit(Value::Bool(true))),
        current_state.clone(),
        vec!["Initial state".to_string()],
    ));

    for (step_idx, step) in scenario.steps.iter().enumerate() {
        for (var, val) in &current_state.vars {
            env.insert(var.clone(), val.clone());
        }

        let successors = next_states(&spec.next, &current_state, &spec.vars, &env, &defs)?;

        let matching = find_matching_transition(&successors, step, &current_state, &defs)?;

        match matching {
            Some((next_state, changes)) => {
                current_state = next_state.clone();
                results.push((step.clone(), next_state, changes));
            }
            None => {
                let available = describe_available_actions(&successors, &current_state);
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

fn build_scenario_env(current: &State, next: &State, constants: &Env) -> Env {
    let mut env = constants.clone();
    for (var, val) in &current.vars {
        env.insert(var.clone(), val.clone());
    }
    for (var, val) in &next.vars {
        let primed_name: Arc<str> = format!("{}'", var).into();
        env.insert(primed_name, val.clone());
    }
    env
}

fn find_matching_transition(
    successors: &[State],
    step: &ScenarioStep,
    current: &State,
    defs: &Definitions,
) -> Result<Option<(State, Vec<String>)>, EvalError> {
    for succ in successors {
        if matches_step(current, succ, step, defs)? {
            let changes = compute_changes(current, succ);
            return Ok(Some((succ.clone(), changes)));
        }
    }
    Ok(None)
}

fn matches_step(
    current: &State,
    next: &State,
    step: &ScenarioStep,
    defs: &Definitions,
) -> Result<bool, EvalError> {
    match step {
        ScenarioStep::Condition(expr) => {
            let env = build_scenario_env(current, next, &Env::new());
            match crate::eval::eval(expr, &env, defs) {
                Ok(Value::Bool(b)) => Ok(b),
                Ok(other) => Err(EvalError::TypeMismatch {
                    expected: "Bool",
                    got: other,
                }),
                Err(e) => Err(e),
            }
        }
    }
}

fn compute_changes(current: &State, next: &State) -> Vec<String> {
    let mut changes = Vec::new();

    for (key, next_val) in &next.vars {
        match current.get(key) {
            Some(curr_val) if curr_val != next_val => {
                changes.push(format!(
                    "{}: {} → {}",
                    key,
                    format_value_compact(curr_val),
                    format_value_compact(next_val)
                ));
            }
            None => {
                changes.push(format!("{}: (new) {}", key, format_value_compact(next_val)));
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

fn describe_available_actions(successors: &[State], current: &State) -> Vec<String> {
    let mut actions = Vec::new();

    for succ in successors {
        let changes = compute_changes(current, succ);
        if !changes.is_empty() {
            let summary = if changes.len() > 2 {
                format!(
                    "{}, ... ({} changes)",
                    changes[..2].join("; "),
                    changes.len()
                )
            } else {
                changes.join("; ")
            };
            actions.push(summary);
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

pub fn format_scenario_result(result: &ScenarioResult, vars_of_interest: &[&str]) -> String {
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
                if let Some(val) = state.get(var) {
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
