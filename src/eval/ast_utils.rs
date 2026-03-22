use std::collections::BTreeSet;
use std::sync::Arc;

use super::Definitions;
use crate::ast::{Expr, Value};
use crate::checker::format_value;

pub(crate) fn format_expr_brief(expr: &Expr) -> String {
    match expr {
        Expr::Lit(Value::Bool(true)) => "TRUE".to_string(),
        Expr::Lit(Value::Bool(false)) => "FALSE".to_string(),
        Expr::Lit(Value::Int(n)) => n.to_string(),
        Expr::Lit(Value::Str(s)) => format!("\"{s}\""),
        Expr::Lit(v) => format_value(v),
        Expr::Var(name) => name.to_string(),
        Expr::Prime(name) => format!("{name}'"),
        Expr::Eq(l, r) => format!("{} = {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Neq(l, r) => format!("{} # {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Lt(l, r) => format!("{} < {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Le(l, r) => format!("{} <= {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Gt(l, r) => format!("{} > {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Ge(l, r) => format!("{} >= {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::In(l, r) => format!("{} \\in {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::NotIn(l, r) => format!("{} \\notin {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::And(l, r) => format!("{} /\\ {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Or(l, r) => format!("{} \\/ {}", format_expr_brief(l), format_expr_brief(r)),
        Expr::Not(e) => format!("~{}", format_expr_brief(e)),
        Expr::FnCall(name, args) => {
            let args_str: Vec<_> = args.iter().map(format_expr_brief).collect();
            if args_str.is_empty() {
                name.to_string()
            } else {
                format!("{}({})", name, args_str.join(", "))
            }
        }
        Expr::FnApp(f, arg) => format!("{}[{}]", format_expr_brief(f), format_expr_brief(arg)),
        Expr::Forall(v, d, b) => format!(
            "\\A {} \\in {}: {}",
            v,
            format_expr_brief(d),
            format_expr_brief(b)
        ),
        Expr::Exists(v, d, b) => format!(
            "\\E {} \\in {}: {}",
            v,
            format_expr_brief(d),
            format_expr_brief(b)
        ),
        _ => "(complex)".to_string(),
    }
}

pub(crate) fn infer_action_name(expr: &Expr, defs: &Definitions) -> Option<Arc<str>> {
    match expr {
        Expr::LabeledAction(label, _) => Some(label.clone()),
        Expr::Var(name) => Some(name.clone()),
        Expr::FnCall(name, _) => Some(name.clone()),
        Expr::Let(_, _, _) => infer_name_from_let_chain(expr, defs),
        Expr::Exists(_, _, body) => infer_action_name(body, defs),
        _ => {
            for (name, (params, body)) in defs {
                if params.is_empty() && body == expr {
                    return Some(name.clone());
                }
            }
            None
        }
    }
}

pub(crate) fn infer_name_from_let_chain(expr: &Expr, defs: &Definitions) -> Option<Arc<str>> {
    let mut inner = expr;
    let mut depth = 0usize;
    while let Expr::Let(_, _, body) = inner {
        inner = body;
        depth += 1;
    }
    for (name, (params, body)) in defs {
        if params.len() == depth && body == inner {
            return Some(name.clone());
        }
    }
    infer_action_name(inner, defs)
}

pub(crate) fn collect_disjuncts_with_labels<'a>(
    expr: &'a Expr,
    defs: &Definitions,
) -> Vec<(&'a Expr, Option<Arc<str>>)> {
    match expr {
        Expr::Or(l, r) => {
            let mut result = collect_disjuncts_with_labels(l, defs);
            result.extend(collect_disjuncts_with_labels(r, defs));
            result
        }
        Expr::LabeledAction(label, action) => vec![(action.as_ref(), Some(label.clone()))],
        Expr::Var(name) => vec![(expr, Some(name.clone()))],
        Expr::FnCall(name, _) => vec![(expr, Some(name.clone()))],
        Expr::Exists(_, _, body) => {
            let label = infer_action_name(body, defs);
            vec![(expr, label)]
        }
        Expr::Let(_, _, _) => {
            let label = infer_name_from_let_chain(expr, defs);
            vec![(expr, label)]
        }
        _ => {
            for (name, (params, body)) in defs {
                if params.is_empty() && body == expr {
                    return vec![(expr, Some(name.clone()))];
                }
            }
            vec![(expr, None)]
        }
    }
}

pub(crate) fn contains_prime_ref(expr: &Expr, defs: &Definitions) -> bool {
    let mut visited = BTreeSet::new();
    contains_prime_ref_impl(expr, defs, &mut visited)
}

fn contains_prime_ref_impl(
    expr: &Expr,
    defs: &Definitions,
    visited: &mut BTreeSet<Arc<str>>,
) -> bool {
    match expr {
        Expr::Prime(_) | Expr::Unchanged(_) => true,
        Expr::Var(_)
        | Expr::Lit(_)
        | Expr::OldValue
        | Expr::Any
        | Expr::EmptyBag
        | Expr::JavaTime
        | Expr::SystemTime => false,
        Expr::Not(e)
        | Expr::Neg(e)
        | Expr::Cardinality(e)
        | Expr::IsFiniteSet(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Len(e)
        | Expr::Head(e)
        | Expr::Tail(e)
        | Expr::TransitiveClosure(e)
        | Expr::ReflexiveTransitiveClosure(e)
        | Expr::SeqSet(e)
        | Expr::PrintT(e)
        | Expr::Permutations(e)
        | Expr::TLCToString(e)
        | Expr::RandomElement(e)
        | Expr::TLCGet(e)
        | Expr::TLCEval(e)
        | Expr::IsABag(e)
        | Expr::BagToSet(e)
        | Expr::SetToBag(e)
        | Expr::BagUnion(e)
        | Expr::SubBag(e)
        | Expr::BagCardinality(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::EnabledOp(e) => contains_prime_ref_impl(e, defs, visited),
        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Implies(l, r)
        | Expr::Equiv(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Le(l, r)
        | Expr::Gt(l, r)
        | Expr::Ge(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::Mod(l, r)
        | Expr::Exp(l, r)
        | Expr::BitwiseAnd(l, r)
        | Expr::ActionCompose(l, r)
        | Expr::In(l, r)
        | Expr::NotIn(l, r)
        | Expr::Union(l, r)
        | Expr::Intersect(l, r)
        | Expr::SetMinus(l, r)
        | Expr::Cartesian(l, r)
        | Expr::Subset(l, r)
        | Expr::ProperSubset(l, r)
        | Expr::Concat(l, r)
        | Expr::Append(l, r)
        | Expr::SetRange(l, r)
        | Expr::FnApp(l, r)
        | Expr::FnMerge(l, r)
        | Expr::SingleFn(l, r)
        | Expr::FunctionSet(l, r)
        | Expr::Print(l, r)
        | Expr::Assert(l, r)
        | Expr::TLCSet(l, r)
        | Expr::SortSeq(l, r)
        | Expr::SelectSeq(l, r)
        | Expr::BagIn(l, r)
        | Expr::BagAdd(l, r)
        | Expr::BagSub(l, r)
        | Expr::BagOfAll(l, r)
        | Expr::CopiesIn(l, r)
        | Expr::SqSubseteq(l, r)
        | Expr::LeadsTo(l, r) => {
            contains_prime_ref_impl(l, defs, visited) || contains_prime_ref_impl(r, defs, visited)
        }
        Expr::If(c, t, e) | Expr::SubSeq(c, t, e) => {
            contains_prime_ref_impl(c, defs, visited)
                || contains_prime_ref_impl(t, defs, visited)
                || contains_prime_ref_impl(e, defs, visited)
        }
        Expr::Forall(_, d, b)
        | Expr::Exists(_, d, b)
        | Expr::Choose(_, d, b)
        | Expr::FnDef(_, d, b)
        | Expr::SetFilter(_, d, b)
        | Expr::SetMap(_, d, b)
        | Expr::CustomOp(_, d, b) => {
            contains_prime_ref_impl(d, defs, visited) || contains_prime_ref_impl(b, defs, visited)
        }
        Expr::SetEnum(elems) | Expr::TupleLit(elems) => elems
            .iter()
            .any(|e| contains_prime_ref_impl(e, defs, visited)),
        Expr::RecordLit(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, e)| contains_prime_ref_impl(e, defs, visited)),
        Expr::RecordAccess(r, _) | Expr::TupleAccess(r, _) => {
            contains_prime_ref_impl(r, defs, visited)
        }
        Expr::Except(b, u) => {
            contains_prime_ref_impl(b, defs, visited)
                || u.iter().any(|(path, val)| {
                    path.iter()
                        .any(|p| contains_prime_ref_impl(p, defs, visited))
                        || contains_prime_ref_impl(val, defs, visited)
                })
        }
        Expr::FnCall(name, args) => {
            if let Some((_, body)) = defs.get(name) {
                if visited.contains(name) {
                    return false;
                }
                visited.insert(name.clone());
                contains_prime_ref_impl(body, defs, visited)
            } else {
                args.iter()
                    .any(|a| contains_prime_ref_impl(a, defs, visited))
            }
        }
        Expr::QualifiedCall(instance_expr, op, _) => match instance_expr.as_ref() {
            Expr::Var(instance_name) => {
                use super::global_state::RESOLVED_INSTANCES;
                RESOLVED_INSTANCES.with(|inst_ref| {
                    let instances = inst_ref.borrow();
                    if let Some(instance_defs) = instances.get(instance_name)
                        && let Some((_, body)) = instance_defs.get(op)
                    {
                        return contains_prime_ref_impl(body, defs, visited);
                    }
                    true
                })
            }
            _ => true,
        },
        Expr::Lambda(_, body) => contains_prime_ref_impl(body, defs, visited),
        Expr::Let(_, binding, body) => {
            contains_prime_ref_impl(binding, defs, visited)
                || contains_prime_ref_impl(body, defs, visited)
        }
        Expr::Case(branches) => branches.iter().any(|(c, r)| {
            contains_prime_ref_impl(c, defs, visited) || contains_prime_ref_impl(r, defs, visited)
        }),
        Expr::LabeledAction(_, a) => contains_prime_ref_impl(a, defs, visited),
        Expr::WeakFairness(_, e)
        | Expr::StrongFairness(_, e)
        | Expr::BoxAction(e, _)
        | Expr::DiamondAction(e, _) => contains_prime_ref_impl(e, defs, visited),
    }
}

pub(crate) fn collect_conjuncts(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::And(l, r) => {
            let mut result = collect_conjuncts(l);
            result.extend(collect_conjuncts(r));
            result
        }
        _ => vec![expr],
    }
}
