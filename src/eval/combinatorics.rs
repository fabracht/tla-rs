use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::Definitions;
use super::core::eval;
use crate::ast::{Env, Expr, Value};

pub(crate) fn permutations(elements: &[Value]) -> Vec<Vec<Value>> {
    if elements.is_empty() {
        return vec![vec![]];
    }
    let mut result = Vec::new();
    for (i, elem) in elements.iter().enumerate() {
        let mut rest: Vec<Value> = elements[..i].to_vec();
        rest.extend(elements[i + 1..].iter().cloned());
        for mut perm in permutations(&rest) {
            perm.insert(0, elem.clone());
            result.push(perm);
        }
    }
    result
}

pub(crate) fn enumerate_subbags(
    elements: &[(Value, i64)],
    idx: usize,
    current: BTreeMap<Value, Value>,
    results: &mut BTreeSet<Value>,
) {
    if idx >= elements.len() {
        results.insert(Value::Fn(current));
        return;
    }
    let (elem, max_count) = &elements[idx];
    for count in 0..=*max_count {
        let mut next = current.clone();
        if count > 0 {
            next.insert(elem.clone(), Value::Int(count));
        }
        enumerate_subbags(elements, idx + 1, next, results);
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum CardinalityConstraint {
    GreaterThan(usize),
    GreaterThanOrEq(usize),
    Equals(usize),
    LessThan(usize),
    LessThanOrEq(usize),
}

pub(crate) fn detect_cardinality_constraint(
    predicate: &Expr,
    var: &Arc<str>,
    env: &mut Env,
    defs: &Definitions,
) -> Option<CardinalityConstraint> {
    fn is_cardinality_of_var(expr: &Expr, var: &Arc<str>) -> bool {
        matches!(expr, Expr::Cardinality(inner) if matches!(inner.as_ref(), Expr::Var(v) if v == var))
    }

    fn try_eval_int(expr: &Expr, env: &mut Env, defs: &Definitions) -> Option<i64> {
        match eval(expr, env, defs) {
            Ok(Value::Int(n)) => Some(n),
            _ => None,
        }
    }

    match predicate {
        Expr::Gt(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::GreaterThan(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::LessThan(n as usize))
            } else if let Expr::Mul(card, two) = l.as_ref()
                && is_cardinality_of_var(card, var)
                && let (Some(mult), Some(rhs)) =
                    (try_eval_int(two, env, defs), try_eval_int(r, env, defs))
                && mult == 2
            {
                Some(CardinalityConstraint::GreaterThan((rhs / 2) as usize))
            } else {
                None
            }
        }
        Expr::Ge(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs)
                    .map(|n| CardinalityConstraint::GreaterThanOrEq(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::LessThanOrEq(n as usize))
            } else {
                None
            }
        }
        Expr::Lt(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::LessThan(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::GreaterThan(n as usize))
            } else {
                None
            }
        }
        Expr::Le(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::LessThanOrEq(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs)
                    .map(|n| CardinalityConstraint::GreaterThanOrEq(n as usize))
            } else {
                None
            }
        }
        Expr::Eq(l, r) => {
            if is_cardinality_of_var(l, var) {
                try_eval_int(r, env, defs).map(|n| CardinalityConstraint::Equals(n as usize))
            } else if is_cardinality_of_var(r, var) {
                try_eval_int(l, env, defs).map(|n| CardinalityConstraint::Equals(n as usize))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(crate) fn k_combinations<T: Clone>(elements: &[T], k: usize) -> Vec<Vec<T>> {
    let n = elements.len();
    if k > n {
        return vec![];
    }
    if k == 0 {
        return vec![vec![]];
    }
    if k == n {
        return vec![elements.to_vec()];
    }

    let mut result = Vec::new();
    let mut indices: Vec<usize> = (0..k).collect();

    loop {
        result.push(indices.iter().map(|&i| elements[i].clone()).collect());

        let mut i = k as i32 - 1;
        while i >= 0 && indices[i as usize] == n - k + i as usize {
            i -= 1;
        }
        if i < 0 {
            break;
        }

        indices[i as usize] += 1;
        for j in (i as usize + 1)..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
    result
}

pub(crate) fn generate_subsets_with_constraint(
    elements: &[Value],
    constraint: CardinalityConstraint,
) -> BTreeSet<Value> {
    let n = elements.len();
    let (min_k, max_k) = match constraint {
        CardinalityConstraint::GreaterThan(k) => (k + 1, n),
        CardinalityConstraint::GreaterThanOrEq(k) => (k, n),
        CardinalityConstraint::Equals(k) => (k, k),
        CardinalityConstraint::LessThan(k) => (0, k.saturating_sub(1)),
        CardinalityConstraint::LessThanOrEq(k) => (0, k),
    };

    let mut result = BTreeSet::new();
    for k in min_k..=max_k.min(n) {
        for combo in k_combinations(elements, k) {
            let subset: BTreeSet<Value> = combo.into_iter().collect();
            result.insert(Value::Set(subset));
        }
    }
    result
}
