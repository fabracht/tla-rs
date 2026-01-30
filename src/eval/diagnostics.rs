use super::Definitions;
use super::ast_utils::format_expr_brief;
use super::core::eval;
use crate::ast::{Env, Expr, InvariantViolationInfo, State, SubExprEval, Value};
use crate::checker::format_value;

pub fn explain_invariant_failure(
    invariant: &Expr,
    state: &State,
    spec: &crate::ast::Spec,
    env: &Env,
    defs: &Definitions,
    inv_name: &str,
) -> Option<InvariantViolationInfo> {
    let mut eval_env = env.clone();
    for (i, var) in spec.vars.iter().enumerate() {
        if let Some(val) = state.values.get(i) {
            eval_env.insert(var.clone(), val.clone());
        }
    }

    match eval(invariant, &mut eval_env, defs) {
        Ok(Value::Bool(true)) => return None,
        Ok(Value::Bool(false)) => {}
        _ => return None,
    }

    let mut info = InvariantViolationInfo {
        name: inv_name.to_string(),
        failing_bindings: Vec::new(),
        subexpression_evals: Vec::new(),
    };

    explain_invariant_impl(invariant, &mut eval_env, defs, &mut info);

    Some(info)
}

fn explain_invariant_impl(
    expr: &Expr,
    env: &mut Env,
    defs: &Definitions,
    info: &mut InvariantViolationInfo,
) {
    match expr {
        Expr::Forall(var, domain, body) => {
            if let Ok(Value::Set(elements)) = eval(domain, env, defs) {
                for elem in elements {
                    env.insert(var.clone(), elem.clone());
                    if let Ok(Value::Bool(false)) = eval(body, env, defs) {
                        info.failing_bindings.push((var.to_string(), elem.clone()));
                        explain_invariant_impl(body, env, defs, info);
                        env.remove(var);
                        return;
                    }
                    env.remove(var);
                }
            }
        }
        Expr::And(l, r) => {
            if let Ok(Value::Bool(false)) = eval(l, env, defs) {
                let expr_str = format_expr_brief(l);
                if let Ok(val) = eval(l, env, defs) {
                    info.subexpression_evals.push(SubExprEval {
                        expression: expr_str,
                        value: val,
                        passed: false,
                    });
                }
                explain_invariant_impl(l, env, defs, info);
            } else {
                let expr_str = format_expr_brief(l);
                if let Ok(val) = eval(l, env, defs) {
                    info.subexpression_evals.push(SubExprEval {
                        expression: expr_str,
                        value: val,
                        passed: true,
                    });
                }
                explain_invariant_impl(r, env, defs, info);
            }
        }
        Expr::Implies(l, r) => {
            if let Ok(Value::Bool(true)) = eval(l, env, defs) {
                let left_str = format_expr_brief(l);
                info.subexpression_evals.push(SubExprEval {
                    expression: format!("{} (antecedent)", left_str),
                    value: Value::Bool(true),
                    passed: true,
                });
                if let Ok(Value::Bool(false)) = eval(r, env, defs) {
                    let right_str = format_expr_brief(r);
                    if let Ok(val) = eval(r, env, defs) {
                        info.subexpression_evals.push(SubExprEval {
                            expression: format!("{} (consequent)", right_str),
                            value: val,
                            passed: false,
                        });
                    }
                    explain_invariant_impl(r, env, defs, info);
                }
            }
        }
        Expr::Eq(l, r) => {
            if let (Ok(lval), Ok(rval)) = (eval(l, env, defs), eval(r, env, defs))
                && lval != rval
            {
                info.subexpression_evals.push(SubExprEval {
                    expression: format!("{} = {}", format_value(&lval), format_value(&rval)),
                    value: Value::Bool(false),
                    passed: false,
                });
            }
        }
        _ => {
            let expr_str = format_expr_brief(expr);
            if let Ok(val) = eval(expr, env, defs) {
                let passed = val == Value::Bool(true);
                info.subexpression_evals.push(SubExprEval {
                    expression: expr_str,
                    value: val,
                    passed,
                });
            }
        }
    }
}
