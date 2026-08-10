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

fn match_def_body(expr: &Expr, defs: &Definitions) -> Option<Arc<str>> {
    for (name, (params, body)) in defs {
        if params.is_empty() && body == expr {
            return Some(name.clone());
        }
    }
    None
}

pub(crate) fn infer_action_name(expr: &Expr, defs: &Definitions) -> Option<Arc<str>> {
    match expr {
        Expr::LabeledAction(label, _) => Some(label.clone()),
        Expr::Var(name) => Some(name.clone()),
        Expr::FnCall(name, _) => Some(name.clone()),
        Expr::Let(_, _, _) => infer_name_from_let_chain(expr, defs),
        Expr::Exists(_, _, body) => {
            infer_action_name(body, defs).or_else(|| match_def_body(expr, defs))
        }
        _ => match_def_body(expr, defs),
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
        Expr::Exists(_, _, _) => {
            let label = infer_action_name(expr, defs);
            vec![(expr, label)]
        }
        Expr::Let(_, _, _) => {
            let label = infer_name_from_let_chain(expr, defs);
            vec![(expr, label)]
        }
        _ => vec![(expr, match_def_body(expr, defs))],
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
        Expr::ChooseUnbounded(_, b) => contains_prime_ref_impl(b, defs, visited),
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
            // Arguments are evaluated in the caller's scope, so a prime in an
            // argument is a real reference regardless of the operator body.
            if args
                .iter()
                .any(|a| contains_prime_ref_impl(a, defs, visited))
            {
                return true;
            }
            match defs.get(name) {
                Some((_, body)) => {
                    if !visited.insert(name.clone()) {
                        // Already on the current resolution path: a recursive
                        // definition we cannot fully inspect here. Over-approximate.
                        return true;
                    }
                    let result = contains_prime_ref_impl(body, defs, visited);
                    visited.remove(name);
                    result
                }
                // Unresolved operator: its body cannot be inspected, so assume
                // it may reference a prime. Over-approximation is the only safe
                // direction — every caller uses this to decide whether to do
                // MORE work (collect candidates, refine), never less.
                None => true,
            }
        }
        Expr::QualifiedCall(instance_expr, op, args) => {
            if args
                .iter()
                .any(|a| contains_prime_ref_impl(a, defs, visited))
            {
                return true;
            }
            match instance_expr.as_ref() {
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
            }
        }
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

pub(crate) fn expr_is_var(expr: &Expr, name: &Arc<str>) -> bool {
    matches!(expr, Expr::Var(n) if n == name)
}

pub(crate) fn expr_references(expr: &Expr, name: &Arc<str>) -> bool {
    match expr {
        Expr::Var(n) => n == name,
        Expr::Lit(_)
        | Expr::Prime(_)
        | Expr::OldValue
        | Expr::Any
        | Expr::EmptyBag
        | Expr::JavaTime
        | Expr::SystemTime
        | Expr::Unchanged(_) => false,
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
        | Expr::EnabledOp(e) => expr_references(e, name),
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
        | Expr::LeadsTo(l, r) => expr_references(l, name) || expr_references(r, name),
        Expr::If(c, t, e) | Expr::SubSeq(c, t, e) => {
            expr_references(c, name) || expr_references(t, name) || expr_references(e, name)
        }
        Expr::Forall(v, d, b)
        | Expr::Exists(v, d, b)
        | Expr::Choose(v, d, b)
        | Expr::FnDef(v, d, b)
        | Expr::SetFilter(v, d, b)
        | Expr::SetMap(v, d, b)
        | Expr::CustomOp(v, d, b) => {
            expr_references(d, name) || (v != name && expr_references(b, name))
        }
        Expr::ChooseUnbounded(v, b) => v != name && expr_references(b, name),
        Expr::SetEnum(elems) | Expr::TupleLit(elems) => {
            elems.iter().any(|e| expr_references(e, name))
        }
        Expr::RecordLit(fields) | Expr::RecordSet(fields) => {
            fields.iter().any(|(_, e)| expr_references(e, name))
        }
        Expr::RecordAccess(r, _) | Expr::TupleAccess(r, _) => expr_references(r, name),
        Expr::Except(b, u) => {
            expr_references(b, name)
                || u.iter().any(|(path, val)| {
                    path.iter().any(|p| expr_references(p, name)) || expr_references(val, name)
                })
        }
        Expr::FnCall(_, args) => args.iter().any(|a| expr_references(a, name)),
        Expr::QualifiedCall(_, _, args) => args.iter().any(|a| expr_references(a, name)),
        Expr::Lambda(params, body) => !params.contains(name) && expr_references(body, name),
        Expr::Let(v, binding, body) => {
            expr_references(binding, name) || (v != name && expr_references(body, name))
        }
        Expr::Case(branches) => branches
            .iter()
            .any(|(c, r)| expr_references(c, name) || expr_references(r, name)),
        Expr::LabeledAction(_, a) => expr_references(a, name),
        Expr::WeakFairness(_, e)
        | Expr::StrongFairness(_, e)
        | Expr::BoxAction(e, _)
        | Expr::DiamondAction(e, _) => expr_references(e, name),
    }
}

#[cfg(test)]
mod prime_ref_tests {
    use super::contains_prime_ref;
    use crate::ast::{Expr, Value};
    use crate::eval::Definitions;
    use std::sync::Arc;

    fn v(name: &str) -> Expr {
        Expr::Var(Arc::from(name))
    }
    fn prime(name: &str) -> Expr {
        Expr::Prime(Arc::from(name))
    }
    fn call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::FnCall(Arc::from(name), args)
    }
    fn defs(entries: Vec<(&str, Vec<&str>, Expr)>) -> Definitions {
        entries
            .into_iter()
            .map(|(n, ps, body)| {
                (
                    Arc::from(n),
                    (ps.into_iter().map(Arc::from).collect(), body),
                )
            })
            .collect()
    }

    #[test]
    fn operator_applied_to_a_prime_argument_has_a_prime() {
        // IsTwice(a) == a = 0  — a prime-free body, but the argument is primed.
        // The prime is at the call site, so the reference is real.
        let d = defs(vec![(
            "IsTwice",
            vec!["a"],
            Expr::Eq(Box::new(v("a")), Box::new(Expr::Lit(Value::Int(0)))),
        )]);
        assert!(contains_prime_ref(&call("IsTwice", vec![prime("y")]), &d));
    }

    #[test]
    fn operator_applied_to_nonprime_arguments_is_prime_free() {
        let d = defs(vec![(
            "IsTwice",
            vec!["a"],
            Expr::Eq(Box::new(v("a")), Box::new(Expr::Lit(Value::Int(0)))),
        )]);
        assert!(!contains_prime_ref(
            &call("IsTwice", vec![Expr::Lit(Value::Int(1))]),
            &d
        ));
    }

    #[test]
    fn operator_with_a_primed_body_has_a_prime() {
        let d = defs(vec![("UsesPrime", vec![], prime("x"))]);
        assert!(contains_prime_ref(&call("UsesPrime", vec![]), &d));
    }

    #[test]
    fn a_recursive_operator_applied_to_a_prime_has_a_prime() {
        // Sum(n) == IF n = 0 THEN 0 ELSE Sum(n)  — self-referential; the cycle
        // must not swallow the primed argument.
        let d = defs(vec![(
            "Sum",
            vec!["n"],
            Expr::If(
                Box::new(Expr::Eq(
                    Box::new(v("n")),
                    Box::new(Expr::Lit(Value::Int(0))),
                )),
                Box::new(Expr::Lit(Value::Int(0))),
                Box::new(call("Sum", vec![v("n")])),
            ),
        )]);
        assert!(contains_prime_ref(&call("Sum", vec![prime("x")]), &d));
    }

    #[test]
    fn an_unresolved_operator_is_over_approximated() {
        // No definition for `Mystery`; its body cannot be inspected, so it must
        // be assumed to reference a prime.
        assert!(contains_prime_ref(
            &call("Mystery", vec![Expr::Lit(Value::Int(1))]),
            &Definitions::new()
        ));
    }
}
