use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ast::Expr;
use crate::eval::Definitions;

pub fn apply_substitutions(module_defs: &Definitions, subs: &[(Arc<str>, Expr)]) -> Definitions {
    let mut result = BTreeMap::new();
    for (name, (params, body)) in module_defs {
        let new_body = substitute_expr(body, subs);
        result.insert(name.clone(), (params.clone(), new_body));
    }
    result
}

fn prime_expr(expr: &Expr) -> Expr {
    let p = |e: &Expr| Box::new(prime_expr(e));
    match expr {
        Expr::Var(name) => Expr::Prime(name.clone()),

        Expr::Lit(_)
        | Expr::Prime(_)
        | Expr::OldValue
        | Expr::JavaTime
        | Expr::SystemTime
        | Expr::Any
        | Expr::EmptyBag => expr.clone(),

        Expr::FnApp(f, a) => Expr::FnApp(p(f), p(a)),
        Expr::RecordAccess(r, field) => Expr::RecordAccess(p(r), field.clone()),
        Expr::TupleAccess(t, idx) => Expr::TupleAccess(p(t), *idx),

        Expr::And(l, r) => Expr::And(p(l), p(r)),
        Expr::Or(l, r) => Expr::Or(p(l), p(r)),
        Expr::Not(e) => Expr::Not(p(e)),
        Expr::Implies(l, r) => Expr::Implies(p(l), p(r)),
        Expr::Equiv(l, r) => Expr::Equiv(p(l), p(r)),
        Expr::Eq(l, r) => Expr::Eq(p(l), p(r)),
        Expr::Neq(l, r) => Expr::Neq(p(l), p(r)),
        Expr::In(l, r) => Expr::In(p(l), p(r)),
        Expr::NotIn(l, r) => Expr::NotIn(p(l), p(r)),

        Expr::Add(l, r) => Expr::Add(p(l), p(r)),
        Expr::Sub(l, r) => Expr::Sub(p(l), p(r)),
        Expr::Mul(l, r) => Expr::Mul(p(l), p(r)),
        Expr::Div(l, r) => Expr::Div(p(l), p(r)),
        Expr::Mod(l, r) => Expr::Mod(p(l), p(r)),
        Expr::Exp(l, r) => Expr::Exp(p(l), p(r)),
        Expr::Neg(e) => Expr::Neg(p(e)),
        Expr::BitwiseAnd(l, r) => Expr::BitwiseAnd(p(l), p(r)),
        Expr::TransitiveClosure(e) => Expr::TransitiveClosure(p(e)),
        Expr::ReflexiveTransitiveClosure(e) => Expr::ReflexiveTransitiveClosure(p(e)),
        Expr::ActionCompose(l, r) => Expr::ActionCompose(p(l), p(r)),
        Expr::Lt(l, r) => Expr::Lt(p(l), p(r)),
        Expr::Le(l, r) => Expr::Le(p(l), p(r)),
        Expr::Gt(l, r) => Expr::Gt(p(l), p(r)),
        Expr::Ge(l, r) => Expr::Ge(p(l), p(r)),

        Expr::SetEnum(elems) => Expr::SetEnum(elems.iter().map(prime_expr).collect()),
        Expr::SetRange(l, r) => Expr::SetRange(p(l), p(r)),
        Expr::SetFilter(var, domain, pred) => Expr::SetFilter(var.clone(), p(domain), p(pred)),
        Expr::SetMap(var, domain, body) => Expr::SetMap(var.clone(), p(domain), p(body)),
        Expr::Union(l, r) => Expr::Union(p(l), p(r)),
        Expr::Intersect(l, r) => Expr::Intersect(p(l), p(r)),
        Expr::SetMinus(l, r) => Expr::SetMinus(p(l), p(r)),
        Expr::Cartesian(l, r) => Expr::Cartesian(p(l), p(r)),
        Expr::Subset(l, r) => Expr::Subset(p(l), p(r)),
        Expr::ProperSubset(l, r) => Expr::ProperSubset(p(l), p(r)),
        Expr::Powerset(e) => Expr::Powerset(p(e)),
        Expr::Cardinality(e) => Expr::Cardinality(p(e)),
        Expr::IsFiniteSet(e) => Expr::IsFiniteSet(p(e)),
        Expr::BigUnion(e) => Expr::BigUnion(p(e)),

        Expr::Exists(var, domain, body) => Expr::Exists(var.clone(), p(domain), p(body)),
        Expr::Forall(var, domain, body) => Expr::Forall(var.clone(), p(domain), p(body)),
        Expr::Choose(var, domain, body) => Expr::Choose(var.clone(), p(domain), p(body)),

        Expr::FnDef(var, domain, body) => Expr::FnDef(var.clone(), p(domain), p(body)),
        Expr::FnCall(name, args) => {
            Expr::FnCall(name.clone(), args.iter().map(prime_expr).collect())
        }
        Expr::Lambda(params, body) => Expr::Lambda(params.clone(), p(body)),
        Expr::FnMerge(l, r) => Expr::FnMerge(p(l), p(r)),
        Expr::SingleFn(l, r) => Expr::SingleFn(p(l), p(r)),
        Expr::CustomOp(name, l, r) => Expr::CustomOp(name.clone(), p(l), p(r)),
        Expr::Except(base, updates) => {
            let new_updates: Vec<_> = updates
                .iter()
                .map(|(keys, val)| {
                    let new_keys: Vec<_> = keys.iter().map(prime_expr).collect();
                    (new_keys, prime_expr(val))
                })
                .collect();
            Expr::Except(p(base), new_updates)
        }
        Expr::Domain(e) => Expr::Domain(p(e)),
        Expr::FunctionSet(l, r) => Expr::FunctionSet(p(l), p(r)),

        Expr::RecordLit(fields) => Expr::RecordLit(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), prime_expr(val)))
                .collect(),
        ),
        Expr::RecordSet(fields) => Expr::RecordSet(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), prime_expr(val)))
                .collect(),
        ),

        Expr::TupleLit(elems) => Expr::TupleLit(elems.iter().map(prime_expr).collect()),

        Expr::Len(e) => Expr::Len(p(e)),
        Expr::Head(e) => Expr::Head(p(e)),
        Expr::Tail(e) => Expr::Tail(p(e)),
        Expr::Append(l, r) => Expr::Append(p(l), p(r)),
        Expr::Concat(l, r) => Expr::Concat(p(l), p(r)),
        Expr::SubSeq(seq, lo, hi) => Expr::SubSeq(p(seq), p(lo), p(hi)),
        Expr::SelectSeq(seq, test) => Expr::SelectSeq(p(seq), p(test)),
        Expr::SeqSet(e) => Expr::SeqSet(p(e)),
        Expr::Print(a, b) => Expr::Print(p(a), p(b)),
        Expr::PrintT(e) => Expr::PrintT(p(e)),
        Expr::Assert(a, b) => Expr::Assert(p(a), p(b)),
        Expr::Permutations(e) => Expr::Permutations(p(e)),
        Expr::SortSeq(a, b) => Expr::SortSeq(p(a), p(b)),
        Expr::TLCToString(e) => Expr::TLCToString(p(e)),
        Expr::RandomElement(e) => Expr::RandomElement(p(e)),
        Expr::TLCGet(e) => Expr::TLCGet(p(e)),
        Expr::TLCSet(a, b) => Expr::TLCSet(p(a), p(b)),
        Expr::TLCEval(e) => Expr::TLCEval(p(e)),

        Expr::IsABag(e) => Expr::IsABag(p(e)),
        Expr::BagToSet(e) => Expr::BagToSet(p(e)),
        Expr::SetToBag(e) => Expr::SetToBag(p(e)),
        Expr::BagIn(l, r) => Expr::BagIn(p(l), p(r)),
        Expr::BagAdd(l, r) => Expr::BagAdd(p(l), p(r)),
        Expr::BagSub(l, r) => Expr::BagSub(p(l), p(r)),
        Expr::BagUnion(e) => Expr::BagUnion(p(e)),
        Expr::SqSubseteq(l, r) => Expr::SqSubseteq(p(l), p(r)),
        Expr::SubBag(e) => Expr::SubBag(p(e)),
        Expr::BagOfAll(l, r) => Expr::BagOfAll(p(l), p(r)),
        Expr::BagCardinality(e) => Expr::BagCardinality(p(e)),
        Expr::CopiesIn(l, r) => Expr::CopiesIn(p(l), p(r)),

        Expr::If(cond, then_br, else_br) => Expr::If(p(cond), p(then_br), p(else_br)),
        Expr::Let(var, binding, body) => Expr::Let(var.clone(), p(binding), p(body)),
        Expr::Case(branches) => Expr::Case(
            branches
                .iter()
                .map(|(cond, result)| (prime_expr(cond), prime_expr(result)))
                .collect(),
        ),

        Expr::Unchanged(_) => expr.clone(),

        Expr::Always(e) => Expr::Always(p(e)),
        Expr::Eventually(e) => Expr::Eventually(p(e)),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(p(l), p(r)),
        Expr::WeakFairness(var, action) => Expr::WeakFairness(var.clone(), p(action)),
        Expr::StrongFairness(var, action) => Expr::StrongFairness(var.clone(), p(action)),
        Expr::BoxAction(action, var) => Expr::BoxAction(p(action), var.clone()),
        Expr::DiamondAction(action, var) => Expr::DiamondAction(p(action), var.clone()),
        Expr::EnabledOp(e) => Expr::EnabledOp(p(e)),

        Expr::QualifiedCall(inst, op, args) => {
            Expr::QualifiedCall(p(inst), op.clone(), args.iter().map(prime_expr).collect())
        }

        Expr::LabeledAction(label, action) => Expr::LabeledAction(label.clone(), p(action)),
    }
}

pub fn substitute_expr(expr: &Expr, subs: &[(Arc<str>, Expr)]) -> Expr {
    match expr {
        Expr::Var(name) => {
            for (param, replacement) in subs {
                if param == name {
                    return replacement.clone();
                }
            }
            Expr::Var(name.clone())
        }

        Expr::And(l, r) => Expr::And(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Not(e) => Expr::Not(Box::new(substitute_expr(e, subs))),
        Expr::Implies(l, r) => Expr::Implies(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Equiv(l, r) => Expr::Equiv(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Eq(l, r) => Expr::Eq(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Neq(l, r) => Expr::Neq(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::In(l, r) => Expr::In(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::NotIn(l, r) => Expr::NotIn(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::Add(l, r) => Expr::Add(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Sub(l, r) => Expr::Sub(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Mul(l, r) => Expr::Mul(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Div(l, r) => Expr::Div(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Mod(l, r) => Expr::Mod(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Exp(l, r) => Expr::Exp(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Neg(e) => Expr::Neg(Box::new(substitute_expr(e, subs))),
        Expr::BitwiseAnd(l, r) => Expr::BitwiseAnd(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::TransitiveClosure(e) => Expr::TransitiveClosure(Box::new(substitute_expr(e, subs))),
        Expr::ReflexiveTransitiveClosure(e) => {
            Expr::ReflexiveTransitiveClosure(Box::new(substitute_expr(e, subs)))
        }
        Expr::ActionCompose(l, r) => Expr::ActionCompose(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Lt(l, r) => Expr::Lt(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Le(l, r) => Expr::Le(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Gt(l, r) => Expr::Gt(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Ge(l, r) => Expr::Ge(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::SetEnum(elems) => {
            Expr::SetEnum(elems.iter().map(|e| substitute_expr(e, subs)).collect())
        }
        Expr::SetRange(l, r) => Expr::SetRange(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SetFilter(var, domain, pred) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::SetFilter(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(pred, &filtered_subs)),
            )
        }
        Expr::SetMap(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::SetMap(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Union(l, r) => Expr::Union(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Intersect(l, r) => Expr::Intersect(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SetMinus(l, r) => Expr::SetMinus(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Cartesian(l, r) => Expr::Cartesian(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Subset(l, r) => Expr::Subset(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::ProperSubset(l, r) => Expr::ProperSubset(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Powerset(e) => Expr::Powerset(Box::new(substitute_expr(e, subs))),
        Expr::Cardinality(e) => Expr::Cardinality(Box::new(substitute_expr(e, subs))),
        Expr::IsFiniteSet(e) => Expr::IsFiniteSet(Box::new(substitute_expr(e, subs))),
        Expr::BigUnion(e) => Expr::BigUnion(Box::new(substitute_expr(e, subs))),

        Expr::Exists(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Exists(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Forall(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Forall(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Choose(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Choose(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }

        Expr::FnApp(f, arg) => Expr::FnApp(
            Box::new(substitute_expr(f, subs)),
            Box::new(substitute_expr(arg, subs)),
        ),
        Expr::FnDef(var, domain, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::FnDef(
                var.clone(),
                Box::new(substitute_expr(domain, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::FnCall(name, args) => Expr::FnCall(
            name.clone(),
            args.iter().map(|a| substitute_expr(a, subs)).collect(),
        ),
        Expr::Lambda(params, body) => {
            let filtered_subs: Vec<_> = subs
                .iter()
                .filter(|(p, _)| !params.contains(p))
                .cloned()
                .collect();
            Expr::Lambda(
                params.clone(),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::FnMerge(l, r) => Expr::FnMerge(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SingleFn(l, r) => Expr::SingleFn(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::CustomOp(name, l, r) => Expr::CustomOp(
            name.clone(),
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Except(base, updates) => {
            let new_updates: Vec<_> = updates
                .iter()
                .map(|(keys, val)| {
                    let new_keys: Vec<_> = keys.iter().map(|k| substitute_expr(k, subs)).collect();
                    (new_keys, substitute_expr(val, subs))
                })
                .collect();
            Expr::Except(Box::new(substitute_expr(base, subs)), new_updates)
        }
        Expr::Domain(e) => Expr::Domain(Box::new(substitute_expr(e, subs))),
        Expr::FunctionSet(l, r) => Expr::FunctionSet(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),

        Expr::RecordLit(fields) => Expr::RecordLit(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordSet(fields) => Expr::RecordSet(
            fields
                .iter()
                .map(|(name, val)| (name.clone(), substitute_expr(val, subs)))
                .collect(),
        ),
        Expr::RecordAccess(rec, field) => {
            Expr::RecordAccess(Box::new(substitute_expr(rec, subs)), field.clone())
        }

        Expr::TupleLit(elems) => {
            Expr::TupleLit(elems.iter().map(|e| substitute_expr(e, subs)).collect())
        }
        Expr::TupleAccess(tup, idx) => {
            Expr::TupleAccess(Box::new(substitute_expr(tup, subs)), *idx)
        }

        Expr::Len(e) => Expr::Len(Box::new(substitute_expr(e, subs))),
        Expr::Head(e) => Expr::Head(Box::new(substitute_expr(e, subs))),
        Expr::Tail(e) => Expr::Tail(Box::new(substitute_expr(e, subs))),
        Expr::Append(l, r) => Expr::Append(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::Concat(l, r) => Expr::Concat(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::SubSeq(seq, start, end) => Expr::SubSeq(
            Box::new(substitute_expr(seq, subs)),
            Box::new(substitute_expr(start, subs)),
            Box::new(substitute_expr(end, subs)),
        ),
        Expr::SelectSeq(seq, test) => Expr::SelectSeq(
            Box::new(substitute_expr(seq, subs)),
            Box::new(substitute_expr(test, subs)),
        ),
        Expr::SeqSet(e) => Expr::SeqSet(Box::new(substitute_expr(e, subs))),

        Expr::If(cond, then_br, else_br) => Expr::If(
            Box::new(substitute_expr(cond, subs)),
            Box::new(substitute_expr(then_br, subs)),
            Box::new(substitute_expr(else_br, subs)),
        ),
        Expr::Let(var, binding, body) => {
            let filtered_subs: Vec<_> = subs.iter().filter(|(p, _)| p != var).cloned().collect();
            Expr::Let(
                var.clone(),
                Box::new(substitute_expr(binding, subs)),
                Box::new(substitute_expr(body, &filtered_subs)),
            )
        }
        Expr::Case(branches) => Expr::Case(
            branches
                .iter()
                .map(|(cond, result)| (substitute_expr(cond, subs), substitute_expr(result, subs)))
                .collect(),
        ),

        Expr::Unchanged(vars) => Expr::Unchanged(vars.clone()),
        Expr::Prime(var) => {
            for (param, replacement) in subs {
                if param == var {
                    return prime_expr(replacement);
                }
            }
            Expr::Prime(var.clone())
        }

        Expr::Always(e) => Expr::Always(Box::new(substitute_expr(e, subs))),
        Expr::Eventually(e) => Expr::Eventually(Box::new(substitute_expr(e, subs))),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(
            Box::new(substitute_expr(l, subs)),
            Box::new(substitute_expr(r, subs)),
        ),
        Expr::WeakFairness(var, action) => {
            Expr::WeakFairness(var.clone(), Box::new(substitute_expr(action, subs)))
        }
        Expr::StrongFairness(var, action) => {
            Expr::StrongFairness(var.clone(), Box::new(substitute_expr(action, subs)))
        }
        Expr::BoxAction(action, var) => {
            Expr::BoxAction(Box::new(substitute_expr(action, subs)), var.clone())
        }
        Expr::DiamondAction(action, var) => {
            Expr::DiamondAction(Box::new(substitute_expr(action, subs)), var.clone())
        }
        Expr::EnabledOp(e) => Expr::EnabledOp(Box::new(substitute_expr(e, subs))),

        Expr::QualifiedCall(inst, op, args) => Expr::QualifiedCall(
            Box::new(substitute_expr(inst, subs)),
            op.clone(),
            args.iter().map(|a| substitute_expr(a, subs)).collect(),
        ),

        Expr::LabeledAction(label, action) => {
            Expr::LabeledAction(label.clone(), Box::new(substitute_expr(action, subs)))
        }

        Expr::Lit(_)
        | Expr::OldValue
        | Expr::Print(_, _)
        | Expr::PrintT(_)
        | Expr::Assert(_, _)
        | Expr::JavaTime
        | Expr::SystemTime
        | Expr::Permutations(_)
        | Expr::SortSeq(_, _)
        | Expr::TLCToString(_)
        | Expr::RandomElement(_)
        | Expr::TLCGet(_)
        | Expr::TLCSet(_, _)
        | Expr::Any
        | Expr::TLCEval(_)
        | Expr::IsABag(_)
        | Expr::BagToSet(_)
        | Expr::SetToBag(_)
        | Expr::BagIn(_, _)
        | Expr::EmptyBag
        | Expr::BagAdd(_, _)
        | Expr::BagSub(_, _)
        | Expr::BagUnion(_)
        | Expr::SqSubseteq(_, _)
        | Expr::SubBag(_)
        | Expr::BagOfAll(_, _)
        | Expr::BagCardinality(_)
        | Expr::CopiesIn(_, _) => expr.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Value;

    fn var(name: &str) -> Arc<str> {
        Arc::from(name)
    }

    fn var_expr(name: &str) -> Expr {
        Expr::Var(var(name))
    }

    fn lit_int(n: i64) -> Expr {
        Expr::Lit(Value::Int(n))
    }

    #[test]
    fn substitute_var_matches() {
        let subs = vec![(var("x"), lit_int(42))];
        let result = substitute_expr(&var_expr("x"), &subs);
        assert_eq!(result, lit_int(42));
    }

    #[test]
    fn substitute_var_no_match() {
        let subs = vec![(var("x"), lit_int(42))];
        let result = substitute_expr(&var_expr("y"), &subs);
        assert_eq!(result, var_expr("y"));
    }

    #[test]
    fn substitute_nested_and() {
        let subs = vec![(var("a"), lit_int(1))];
        let expr = Expr::And(
            Box::new(Expr::Eq(Box::new(var_expr("a")), Box::new(lit_int(0)))),
            Box::new(var_expr("b")),
        );
        let result = substitute_expr(&expr, &subs);
        let expected = Expr::And(
            Box::new(Expr::Eq(Box::new(lit_int(1)), Box::new(lit_int(0)))),
            Box::new(var_expr("b")),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_respects_binding_scope() {
        let subs = vec![(var("x"), lit_int(99))];
        let expr = Expr::Exists(
            var("x"),
            Box::new(Expr::SetEnum(vec![lit_int(1), lit_int(2)])),
            Box::new(Expr::Eq(Box::new(var_expr("x")), Box::new(lit_int(1)))),
        );
        let result = substitute_expr(&expr, &subs);
        if let Expr::Exists(_, _, body) = &result {
            assert_eq!(
                **body,
                Expr::Eq(Box::new(var_expr("x")), Box::new(lit_int(1)))
            );
        } else {
            panic!("expected Exists");
        }
    }

    #[test]
    fn substitute_let_binding_scope() {
        let subs = vec![(var("x"), lit_int(99))];
        let expr = Expr::Let(var("x"), Box::new(lit_int(5)), Box::new(var_expr("x")));
        let result = substitute_expr(&expr, &subs);
        if let Expr::Let(_, binding, body) = &result {
            assert_eq!(**binding, lit_int(5));
            assert_eq!(**body, var_expr("x"));
        } else {
            panic!("expected Let");
        }
    }

    #[test]
    fn apply_substitutions_replaces_in_defs() {
        let mut defs: Definitions = BTreeMap::new();
        defs.insert(
            var("Op"),
            (
                vec![],
                Expr::Add(Box::new(var_expr("N")), Box::new(lit_int(1))),
            ),
        );
        let subs = vec![(var("N"), lit_int(10))];
        let result = apply_substitutions(&defs, &subs);
        let (_, body) = result.get(&var("Op")).expect("Op should exist");
        assert_eq!(
            *body,
            Expr::Add(Box::new(lit_int(10)), Box::new(lit_int(1)))
        );
    }

    #[test]
    fn substitute_literal_unchanged() {
        let subs = vec![(var("x"), var_expr("y"))];
        let result = substitute_expr(&lit_int(42), &subs);
        assert_eq!(result, lit_int(42));
    }

    #[test]
    fn substitute_if_then_else() {
        let subs = vec![(var("c"), Expr::Lit(Value::Bool(true)))];
        let expr = Expr::If(
            Box::new(var_expr("c")),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        let result = substitute_expr(&expr, &subs);
        let expected = Expr::If(
            Box::new(Expr::Lit(Value::Bool(true))),
            Box::new(lit_int(1)),
            Box::new(lit_int(2)),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn prime_simple_var() {
        let result = prime_expr(&var_expr("x"));
        assert_eq!(result, Expr::Prime(var("x")));
    }

    #[test]
    fn prime_fn_app() {
        let expr = Expr::FnApp(Box::new(var_expr("channels")), Box::new(lit_int(1)));
        let result = prime_expr(&expr);
        let expected = Expr::FnApp(Box::new(Expr::Prime(var("channels"))), Box::new(lit_int(1)));
        assert_eq!(result, expected);
    }

    #[test]
    fn prime_binary_add() {
        let expr = Expr::Add(Box::new(var_expr("a")), Box::new(var_expr("b")));
        let result = prime_expr(&expr);
        let expected = Expr::Add(
            Box::new(Expr::Prime(var("a"))),
            Box::new(Expr::Prime(var("b"))),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn prime_if_then_else() {
        let expr = Expr::If(
            Box::new(var_expr("cond")),
            Box::new(var_expr("a")),
            Box::new(var_expr("b")),
        );
        let result = prime_expr(&expr);
        let expected = Expr::If(
            Box::new(Expr::Prime(var("cond"))),
            Box::new(Expr::Prime(var("a"))),
            Box::new(Expr::Prime(var("b"))),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn prime_literal_unchanged() {
        let expr = lit_int(42);
        let result = prime_expr(&expr);
        assert_eq!(result, lit_int(42));
    }

    #[test]
    fn prime_record_access() {
        let expr = Expr::RecordAccess(Box::new(var_expr("state")), var("field"));
        let result = prime_expr(&expr);
        let expected = Expr::RecordAccess(Box::new(Expr::Prime(var("state"))), var("field"));
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_prime_with_binary_replacement() {
        let subs = vec![(
            var("x"),
            Expr::Add(Box::new(var_expr("a")), Box::new(var_expr("b"))),
        )];
        let expr = Expr::Prime(var("x"));
        let result = substitute_expr(&expr, &subs);
        let expected = Expr::Add(
            Box::new(Expr::Prime(var("a"))),
            Box::new(Expr::Prime(var("b"))),
        );
        assert_eq!(result, expected);
    }
}
