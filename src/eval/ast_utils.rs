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

/// A parameterized `LET F(p1, ..) == body` operator, which the parser encodes as
/// `Let("_params", TupleLit([p1, ..]), body)`. Returns its parameter names and
/// body so a caller can register it as a definition; `None` for a plain LET value.
pub(crate) fn parameterized_let_op(binding: &Expr) -> Option<(Vec<Arc<str>>, &Expr)> {
    if let Expr::Let(marker, params_tuple, body) = binding
        && marker.as_ref() == "_params"
        && let Expr::TupleLit(param_exprs) = params_tuple.as_ref()
    {
        let params: Option<Vec<Arc<str>>> = param_exprs
            .iter()
            .map(|e| match e {
                Expr::Var(n) => Some(n.clone()),
                _ => None,
            })
            .collect();
        return params.map(|p| (p, body.as_ref()));
    }
    None
}

fn match_def_body(expr: &Expr, defs: &Definitions) -> Option<Arc<str>> {
    for (name, (params, body)) in defs {
        if params.is_empty() && body.as_ref() == expr {
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
        if params.len() == depth && body.as_ref() == inner {
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
    let is_prime = |e: &Expr| matches!(e, Expr::Prime(_) | Expr::Unchanged(_));
    refers_through_defs(expr, defs, &mut visited, &is_prime)
}

/// Whether `expr` can take different values in different states: it refers to a
/// state variable (or primes one), `ENABLED`, or a built-in whose value depends on
/// the run (`TLCGet`, `RandomElement`, time), directly or through the definitions it
/// calls. A call to an unknown operator counts as a reference.
pub(crate) fn references_state(expr: &Expr, vars: &[Arc<str>], defs: &Definitions) -> bool {
    let mut visited = BTreeSet::new();
    let is_state = |e: &Expr| match e {
        Expr::Prime(_)
        | Expr::Unchanged(_)
        | Expr::EnabledOp(_)
        | Expr::TLCGet(_)
        | Expr::RandomElement(_)
        | Expr::JavaTime
        | Expr::SystemTime => true,
        Expr::Var(name) => vars.contains(name),
        _ => false,
    };
    refers_through_defs(expr, defs, &mut visited, &is_state)
}

/// Whether `expr` contains a temporal operator, directly or through the definitions
/// it calls.
pub(crate) fn reaches_temporal(expr: &Expr, defs: &Definitions) -> bool {
    let mut visited = BTreeSet::new();
    let is_temporal = |e: &Expr| {
        matches!(
            e,
            Expr::Always(_)
                | Expr::Eventually(_)
                | Expr::LeadsTo(_, _)
                | Expr::WeakFairness(_, _)
                | Expr::StrongFairness(_, _)
                | Expr::BoxAction(_, _)
                | Expr::DiamondAction(_, _)
        )
    };
    refers_through_defs(expr, defs, &mut visited, &is_temporal)
}

/// Whether some subexpression satisfies `leaf`, following zero-argument and
/// parameterized definitions (each at most once per path). A call to an unknown
/// operator counts as satisfying it.
fn refers_through_defs(
    expr: &Expr,
    defs: &Definitions,
    visited: &mut BTreeSet<Arc<str>>,
    leaf: &dyn Fn(&Expr) -> bool,
) -> bool {
    if leaf(expr) {
        return true;
    }
    match expr {
        Expr::Prime(_) | Expr::Unchanged(_) => false,
        Expr::Var(name) => match defs.get(name) {
            Some((params, body)) if params.is_empty() => {
                if !visited.insert(name.clone()) {
                    return false;
                }
                let result = refers_through_defs(body, defs, visited, leaf);
                visited.remove(name);
                result
            }
            _ => false,
        },
        Expr::Lit(_)
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
        | Expr::EnabledOp(e) => refers_through_defs(e, defs, visited, leaf),
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
            refers_through_defs(l, defs, visited, leaf)
                || refers_through_defs(r, defs, visited, leaf)
        }
        Expr::If(c, t, e) | Expr::SubSeq(c, t, e) => {
            refers_through_defs(c, defs, visited, leaf)
                || refers_through_defs(t, defs, visited, leaf)
                || refers_through_defs(e, defs, visited, leaf)
        }
        Expr::Forall(_, d, b)
        | Expr::Exists(_, d, b)
        | Expr::Choose(_, d, b)
        | Expr::FnDef(_, d, b)
        | Expr::SetFilter(_, d, b)
        | Expr::SetMap(_, d, b)
        | Expr::CustomOp(_, d, b) => {
            refers_through_defs(d, defs, visited, leaf)
                || refers_through_defs(b, defs, visited, leaf)
        }
        Expr::ChooseUnbounded(_, b) => refers_through_defs(b, defs, visited, leaf),
        Expr::SetEnum(elems) | Expr::TupleLit(elems) => elems
            .iter()
            .any(|e| refers_through_defs(e, defs, visited, leaf)),
        Expr::RecordLit(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, e)| refers_through_defs(e, defs, visited, leaf)),
        Expr::RecordAccess(r, _) | Expr::TupleAccess(r, _) => {
            refers_through_defs(r, defs, visited, leaf)
        }
        Expr::Except(b, u) => {
            refers_through_defs(b, defs, visited, leaf)
                || u.iter().any(|(path, val)| {
                    path.iter()
                        .any(|p| refers_through_defs(p, defs, visited, leaf))
                        || refers_through_defs(val, defs, visited, leaf)
                })
        }
        Expr::FnCall(name, args) => {
            if args
                .iter()
                .any(|a| refers_through_defs(a, defs, visited, leaf))
            {
                return true;
            }
            match defs.get(name) {
                Some((_, body)) => {
                    if !visited.insert(name.clone()) {
                        return false;
                    }
                    let result = refers_through_defs(body, defs, visited, leaf);
                    visited.remove(name);
                    result
                }
                None => true,
            }
        }
        Expr::QualifiedCall(instance_expr, op, args) => {
            if args
                .iter()
                .any(|a| refers_through_defs(a, defs, visited, leaf))
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
                            let marker: Arc<str> = Arc::from(format!("{instance_name}!{op}"));
                            if !visited.insert(marker.clone()) {
                                return false;
                            }
                            let result = refers_through_defs(body, defs, visited, leaf);
                            visited.remove(&marker);
                            return result;
                        }
                        true
                    })
                }
                _ => true,
            }
        }
        Expr::Lambda(_, body) => refers_through_defs(body, defs, visited, leaf),
        Expr::Let(_, binding, body) => {
            refers_through_defs(binding, defs, visited, leaf)
                || refers_through_defs(body, defs, visited, leaf)
        }
        Expr::Case(branches) => branches.iter().any(|(c, r)| {
            refers_through_defs(c, defs, visited, leaf)
                || refers_through_defs(r, defs, visited, leaf)
        }),
        Expr::LabeledAction(_, a) => refers_through_defs(a, defs, visited, leaf),
        Expr::WeakFairness(a, b)
        | Expr::StrongFairness(a, b)
        | Expr::BoxAction(a, b)
        | Expr::DiamondAction(a, b) => {
            refers_through_defs(a, defs, visited, leaf)
                || refers_through_defs(b, defs, visited, leaf)
        }
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

pub(crate) fn cartesian_operands<'a>(l: &'a Expr, r: &'a Expr) -> Vec<&'a Expr> {
    fn walk_left<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
        match e {
            Expr::Cartesian(ll, lr) => {
                walk_left(ll, out);
                out.push(lr);
            }
            _ => out.push(e),
        }
    }
    let mut out = Vec::new();
    walk_left(l, &mut out);
    out.push(r);
    out
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
        Expr::WeakFairness(a, b)
        | Expr::StrongFairness(a, b)
        | Expr::BoxAction(a, b)
        | Expr::DiamondAction(a, b) => expr_references(a, name) || expr_references(b, name),
    }
}

pub(crate) fn expr_contains(haystack: &Expr, needle: &Expr) -> bool {
    if haystack == needle {
        return true;
    }
    match haystack {
        Expr::Lit(_)
        | Expr::Var(_)
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
        | Expr::EnabledOp(e) => expr_contains(e, needle),
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
        | Expr::LeadsTo(l, r) => expr_contains(l, needle) || expr_contains(r, needle),
        Expr::If(c, t, e) | Expr::SubSeq(c, t, e) => {
            expr_contains(c, needle) || expr_contains(t, needle) || expr_contains(e, needle)
        }
        Expr::Forall(_, d, b)
        | Expr::Exists(_, d, b)
        | Expr::Choose(_, d, b)
        | Expr::FnDef(_, d, b)
        | Expr::SetFilter(_, d, b)
        | Expr::SetMap(_, d, b)
        | Expr::CustomOp(_, d, b) => expr_contains(d, needle) || expr_contains(b, needle),
        Expr::ChooseUnbounded(_, b) => expr_contains(b, needle),
        Expr::SetEnum(elems) | Expr::TupleLit(elems) => {
            elems.iter().any(|e| expr_contains(e, needle))
        }
        Expr::RecordLit(fields) | Expr::RecordSet(fields) => {
            fields.iter().any(|(_, e)| expr_contains(e, needle))
        }
        Expr::RecordAccess(r, _) | Expr::TupleAccess(r, _) => expr_contains(r, needle),
        Expr::Except(b, u) => {
            expr_contains(b, needle)
                || u.iter().any(|(path, val)| {
                    path.iter().any(|p| expr_contains(p, needle)) || expr_contains(val, needle)
                })
        }
        Expr::FnCall(_, args) | Expr::QualifiedCall(_, _, args) => {
            args.iter().any(|a| expr_contains(a, needle))
        }
        Expr::Lambda(_, body) => expr_contains(body, needle),
        Expr::Let(_, binding, body) => {
            expr_contains(binding, needle) || expr_contains(body, needle)
        }
        Expr::Case(branches) => branches
            .iter()
            .any(|(c, r)| expr_contains(c, needle) || expr_contains(r, needle)),
        Expr::LabeledAction(_, a) => expr_contains(a, needle),
        Expr::WeakFairness(a, b)
        | Expr::StrongFairness(a, b)
        | Expr::BoxAction(a, b)
        | Expr::DiamondAction(a, b) => expr_contains(a, needle) || expr_contains(b, needle),
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
                    (ps.into_iter().map(Arc::from).collect(), Arc::new(body)),
                )
            })
            .collect()
    }

    #[test]
    fn operator_applied_to_a_prime_argument_has_a_prime() {
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
        assert!(contains_prime_ref(
            &call("Mystery", vec![Expr::Lit(Value::Int(1))]),
            &Definitions::new()
        ));
    }
}
