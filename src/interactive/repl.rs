use std::sync::Arc;

use crate::ast::Env;
use crate::ast::{Spec, State, Value};
use crate::checker::format_value;
use crate::eval::{Definitions, eval, make_primed_names};

pub(super) fn eval_repl(
    input: &str,
    current: &State,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
) -> String {
    let expr = match crate::parser::parse_expr(input) {
        Ok(e) => e,
        Err(e) => return format!("Parse error: {}", e.message),
    };

    let mut eval_env = env.clone();
    for (i, var) in spec.vars.iter().enumerate() {
        if let Some(val) = current.values.get(i) {
            eval_env.insert(var.clone(), val.clone());
        }
    }

    match eval(&expr, &mut eval_env, defs) {
        Ok(val) => format!("= {}", format_value(&val)),
        Err(e) => format!("Error: {:?}", e),
    }
}

pub(super) fn test_hypothesis(
    guard_expr: &str,
    history: &[(State, Option<Arc<str>>)],
    current: &State,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
) -> String {
    let expr = match crate::parser::parse_expr(guard_expr) {
        Ok(e) => e,
        Err(e) => return format!("Parse error: {}", e.message),
    };

    let mut blocked_transitions: Vec<(usize, String)> = Vec::new();
    let primed_vars = make_primed_names(&spec.vars);

    let mut prev_state = if let Some((first_state, _)) = history.first() {
        first_state.clone()
    } else {
        return "No history to test hypothesis against".to_string();
    };

    for (i, (next_state, action)) in history
        .iter()
        .skip(1)
        .chain(std::iter::once(&(current.clone(), None)))
        .enumerate()
    {
        let mut eval_env = env.clone();
        for (vi, var) in spec.vars.iter().enumerate() {
            if let Some(val) = prev_state.values.get(vi) {
                eval_env.insert(var.clone(), val.clone());
            }
            if let Some(val) = next_state.values.get(vi) {
                eval_env.insert(primed_vars[vi].clone(), val.clone());
            }
        }

        match eval(&expr, &mut eval_env, defs) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                let action_name = action
                    .as_ref()
                    .map(|a| a.to_string())
                    .unwrap_or_else(|| "(unnamed)".to_string());
                blocked_transitions.push((i, action_name));
            }
            Ok(other) => return format!("Hypothesis must evaluate to Bool, got {:?}", other),
            Err(e) => return format!("Error evaluating hypothesis: {:?}", e),
        }

        prev_state = next_state.clone();
    }

    if blocked_transitions.is_empty() {
        format!(
            "Hypothesis '{}' would NOT have blocked any transitions",
            guard_expr
        )
    } else {
        let mut result = format!(
            "Hypothesis '{}' would have blocked {} transition(s):\n",
            guard_expr,
            blocked_transitions.len()
        );
        for (i, action) in blocked_transitions.iter().take(5) {
            result.push_str(&format!(
                "  State {} -> {}: {} would be BLOCKED\n",
                i,
                i + 1,
                action
            ));
        }
        if blocked_transitions.len() > 5 {
            result.push_str(&format!(
                "  ... and {} more\n",
                blocked_transitions.len() - 5
            ));
        }
        result.push_str("\nBug might have been prevented!");
        result
    }
}
