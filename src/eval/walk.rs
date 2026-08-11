//! Continuation-passing next-state generation, a port of TLC's `getNextStates`.
//!
//! Instead of inferring a candidate set per primed variable and filtering the
//! cross product (which can only ever *reject*, so any inference shortfall is a
//! silent false pass), this walks the next-state relation over a single partial
//! successor state. A primed variable is *bound* at the conjunct that assigns
//! it; `\/`, `\E`, `\in`, `IF`/`CASE` branch the recursion; a successor is
//! emitted only when the whole relation has been discharged with every variable
//! assigned. Dependencies like `b' = a' + 10` need no analysis: `a'` is already
//! bound when `b'`'s conjunct is reached.
//!
//! Gated behind `TLA_WALK` while both engines coexist (design commits 3–10).

use std::sync::Arc;

use super::Definitions;
use super::core::{eval, expand_unchanged_vars};
use super::error::{EvalError, Result};
use super::helpers::{eval_bool, eval_set, update_nested_value};
use super::state::env_to_next_state;
use crate::ast::{Env, Expr, Transition, Value};
use crate::intern::primed_name;
use crate::substitution::substitute_expr;

/// Whether the walker engine is selected.
pub(crate) fn walk_enabled() -> bool {
    std::env::var_os("TLA_WALK").is_some()
}

/// Whether the walker is generating successors (`x' = e` binds `x'`) or initial
/// states (`x = e` binds `x`). The machine is otherwise identical, as in TLC.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    Next,
    Init,
}

pub(crate) struct WalkCtx<'a> {
    pub vars: &'a [Arc<str>],
    /// The env keys the emitted state is read from — the primed names for
    /// `Next`, the bare variable names for `Init`.
    pub state_keys: &'a [Arc<str>],
    pub defs: &'a Definitions,
    pub phase: Phase,
    /// Whether a successor requires *every* variable assigned. Generating states
    /// (`Next`/`Init`) demands totality — an unassigned variable is not a state.
    /// `ENABLED A` is `\E vars' : A`, so a partial assignment is a legitimate
    /// witness; there totality is not required and the walk short-circuits on the
    /// first witness.
    pub require_total: bool,
}

impl WalkCtx<'_> {
    /// True once a witness has been found and no further search is needed
    /// (the `ENABLED` case).
    fn satisfied(&self, run: &Run<'_>) -> bool {
        !self.require_total && !run.results.is_empty()
    }
}

impl WalkCtx<'_> {
    /// The env key an assignment to state variable `name` binds.
    fn key_for(&self, name: &Arc<str>) -> Arc<str> {
        match self.phase {
            Phase::Next => primed_name(name),
            Phase::Init => name.clone(),
        }
    }

    /// If `expr` is an assignment target for this phase — a prime (`Next`) or a
    /// bare state variable (`Init`), possibly indexed — return its base name and
    /// key path.
    fn assign_target(&self, expr: &Expr) -> Option<(Arc<str>, Vec<Expr>)> {
        match self.phase {
            Phase::Next => prime_target(expr),
            Phase::Init => init_target(expr, self.vars),
        }
    }
}

/// The conjuncts still to be discharged, newest first — TLC's `ActionItemList`.
/// `Slice` carries a block of owned conjuncts (from `\A` expansion or `UNCHANGED`
/// desugaring) without allocating a node per item. The `usize` is the scope
/// mark: the shadow-journal length when the item was pushed, so it can be
/// discharged in the scope it was written in (see `discharge`).
enum Cont<'a> {
    Nil,
    Cons(&'a Expr, usize, &'a Cont<'a>),
    Slice(&'a [Expr], usize, &'a Cont<'a>),
}

/// The mutable state of one walk: the label to attribute to each successor, the
/// sink they are collected into, and the shadow journal.
///
/// The journal records every quantifier binding that *overwrites* an existing
/// name (`(name, value it shadowed)`). A continuation item pushed at scope mark
/// `m` must be evaluated with the bindings that were live at `m`, not whatever
/// an intervening quantifier rebound — TLC gives every continuation node its own
/// context; the journal reconstructs that with one flat env. See `discharge`.
struct Run<'r> {
    action: Option<Arc<str>>,
    results: &'r mut Vec<Transition>,
    journal: Vec<(Arc<str>, Option<Value>)>,
}

/// Walk one action (a top-level disjunct, already labelled by the caller) and
/// append every successor it produces.
pub(crate) fn walk_next(
    action_expr: &Expr,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    action: Option<Arc<str>>,
    results: &mut Vec<Transition>,
) -> Result<()> {
    let mut run = Run {
        action,
        results,
        journal: Vec::new(),
    };
    walk(action_expr, &Cont::Nil, env, ctx, &mut run)
}

/// Walk the Init predicate over one partial state, binding unprimed variables,
/// and return the distinct initial states. The same machine as `walk_next`, so
/// `\E`/`IF`/`LET`/operator calls in Init branch exactly as they do in Next.
pub(crate) fn walk_init(
    init: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    defs: &Definitions,
) -> Result<Vec<crate::ast::State>> {
    let ctx = WalkCtx {
        vars,
        state_keys: vars,
        defs,
        phase: Phase::Init,
        require_total: true,
    };
    let mut results = Vec::new();
    {
        let mut run = Run {
            action: None,
            results: &mut results,
            journal: Vec::new(),
        };
        walk(init, &Cont::Nil, env, &ctx, &mut run)?;
    }
    let mut seen = indexmap::IndexSet::new();
    for t in results {
        seen.insert(t.state);
    }
    Ok(seen.into_iter().collect())
}

/// `ENABLED action` in the current state: does the action have any successor?
/// `ENABLED A` is `\E vars' : A`, so a partial assignment counts — an action
/// that leaves some variable unconstrained is still enabled.
pub(crate) fn walk_action_enabled(
    action: &Expr,
    env: &mut Env,
    vars: &[Arc<str>],
    state_keys: &[Arc<str>],
    defs: &Definitions,
) -> Result<bool> {
    let ctx = WalkCtx {
        vars,
        state_keys,
        defs,
        phase: Phase::Next,
        require_total: false,
    };
    let mut results = Vec::new();
    let mut run = Run {
        action: None,
        results: &mut results,
        journal: Vec::new(),
    };
    walk(action, &Cont::Nil, env, &ctx, &mut run)?;
    Ok(!results.is_empty())
}

fn walk(
    node: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    if ctx.satisfied(run) {
        return Ok(());
    }
    match node {
        // Conjunction: discharge left-to-right. Push the rest onto the
        // continuation and recurse into the head, so every later conjunct sees
        // the primes the earlier ones bound.
        Expr::And(l, r) => {
            let mark = run.journal.len();
            walk(l, &Cont::Cons(r, mark, cont), env, ctx, run)
        }

        // Disjunction: each branch explored with the same continuation and the
        // same partial successor.
        Expr::Or(l, r) => {
            walk(l, cont, env, ctx, run)?;
            walk(r, cont, env, ctx, run)
        }

        // A named-but-unparameterised action reference, or an action operator:
        // substitute the arguments into the body and walk it.
        Expr::Var(name) => match ctx.defs.get(name) {
            Some((params, body)) if params.is_empty() => walk(&body.clone(), cont, env, ctx, run),
            _ => walk_bool(node, cont, env, ctx, run),
        },
        Expr::FnCall(name, args) => match ctx.defs.get(name) {
            Some((params, body)) if params.len() == args.len() => {
                let subs: Vec<(Arc<str>, Expr)> =
                    params.iter().cloned().zip(args.iter().cloned()).collect();
                walk(&substitute_expr(body, &subs), cont, env, ctx, run)
            }
            _ => walk_bool(node, cont, env, ctx, run),
        },
        Expr::LabeledAction(_, inner) => walk(inner, cont, env, ctx, run),

        // Instance operator in action position: resolve the operator body (with
        // WITH-substitutions and, for parameterized instances, the instance
        // arguments applied), substitute the call arguments, and walk it.
        Expr::QualifiedCall(instance_expr, op, args) => {
            walk_qualified_call(instance_expr, op, args, cont, env, ctx, run)
        }

        // Existential in action position: one branch per witness. The binding
        // is journalled so a continuation item pushed in an enclosing scope that
        // is discharged inside this `\E` still sees its own binding, not ours.
        Expr::Exists(var, domain, body) => {
            let dom = eval_set(domain, env, ctx.defs)?;
            for val in dom {
                if ctx.satisfied(run) {
                    break;
                }
                let shadowed = env.insert(var.clone(), val);
                run.journal.push((var.clone(), shadowed));
                let r = walk(body, cont, env, ctx, run);
                let (name, prev) = run.journal.pop().expect("journal balanced");
                restore(env, &name, prev);
                r?;
            }
            Ok(())
        }

        // Universal in action position: the body must hold for every element,
        // so expand to a conjunction over the (concrete) domain.
        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, ctx.defs)?;
            let items: Vec<Expr> = dom
                .into_iter()
                .map(|val| substitute_expr(body, &[(var.clone(), Expr::Lit(val))]))
                .collect();
            let mark = run.journal.len();
            advance(&Cont::Slice(&items, mark, cont), env, ctx, run)
        }

        // UNCHANGED assigns each variable its pre-state value (the evaluator's
        // own arm is a *constraint*, which needs the primes already bound).
        Expr::Unchanged(vars) => {
            let items: Vec<Expr> = expand_unchanged_vars(vars, ctx.defs)
                .into_iter()
                .map(|v| Expr::Eq(Box::new(Expr::Prime(v.clone())), Box::new(Expr::Var(v))))
                .collect();
            let mark = run.journal.len();
            advance(&Cont::Slice(&items, mark, cont), env, ctx, run)
        }

        // IF: guard is a boolean read in the current partial state; recurse into
        // exactly one branch.
        Expr::If(c, t, e) => {
            if eval_bool(c, env, ctx.defs)? {
                walk(t, cont, env, ctx, run)
            } else {
                walk(e, cont, env, ctx, run)
            }
        }

        // CASE: first branch whose guard holds; a non-exhaustive CASE is a hard
        // error (as in the evaluator).
        Expr::Case(branches) => {
            for (guard, body) in branches {
                if eval_bool(guard, env, ctx.defs)? {
                    return walk(body, cont, env, ctx, run);
                }
            }
            Err(EvalError::domain_error("CASE: no matching branch"))
        }

        // LET: bind the definition into the body and walk it.
        Expr::Let(name, binding, body) => {
            let bound = substitute_expr(body, &[(name.clone(), (**binding).clone())]);
            walk(&bound, cont, env, ctx, run)
        }

        // Equality: an assignment when one side is an (indexed) unbound prime,
        // a constraint otherwise.
        Expr::Eq(l, r) => walk_eq(node, l, r, cont, env, ctx, run),

        // Membership: a binding construct that enumerates the set when the
        // element is an unbound prime, a constraint otherwise.
        Expr::In(elem, set) => walk_in(node, elem, set, cont, env, ctx, run),

        // Everything else is a boolean predicate: evaluate, prune on false.
        _ => walk_bool(node, cont, env, ctx, run),
    }
}

/// Discharge the continuation: pop the next pending conjunct, or run a
/// successor if none remain.
fn advance(cont: &Cont<'_>, env: &mut Env, ctx: &WalkCtx<'_>, run: &mut Run<'_>) -> Result<()> {
    match cont {
        Cont::Cons(head, mark, tail) => discharge(head, tail, *mark, env, ctx, run),
        Cont::Slice(items, mark, tail) => match items.split_first() {
            None => advance(tail, env, ctx, run),
            Some((head, rest)) => {
                discharge(head, &Cont::Slice(rest, *mark, tail), *mark, env, ctx, run)
            }
        },
        Cont::Nil => {
            // Generating a state requires every variable assigned — the walker
            // never invents a stutter for an unassigned variable (a loud
            // diagnostic for that lands in a later commit). `ENABLED`
            // (require_total = false) accepts a partial assignment as a witness.
            if !ctx.require_total || ctx.state_keys.iter().all(|k| env.get(k).is_some()) {
                run.results.push(Transition {
                    state: env_to_next_state(env, ctx.vars, ctx.state_keys),
                    action: run.action.clone(),
                });
            }
            Ok(())
        }
    }
}

/// Discharge a continuation item that was pushed at scope `mark`. The journal
/// may have grown since — quantifiers entered between the push and now — so
/// unwind those shadowing bindings to reconstruct the scope the item was written
/// in, walk it, then redo them so the enclosing scopes see their own bindings
/// again (sibling disjuncts and the quantifier loops depend on it).
fn discharge(
    head: &Expr,
    tail: &Cont<'_>,
    mark: usize,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    // Fast path: nothing was shadowed since the item was pushed.
    if run.journal.len() == mark {
        return walk(head, tail, env, ctx, run);
    }

    // Unwind to `mark`, remembering both the shadowed value (to redo the
    // journal) and the shadowing value currently in env (to redo env).
    let mut undone: Vec<(Arc<str>, Option<Value>, Option<Value>)> = Vec::new();
    while run.journal.len() > mark {
        let (name, shadowed) = run.journal.pop().expect("journal longer than mark");
        let shadowing = env.get(&name).cloned();
        restore(env, &name, shadowed.clone());
        undone.push((name, shadowed, shadowing));
    }

    let r = walk(head, tail, env, ctx, run);

    // Redo, bottom-of-the-unwound-suffix first, restoring env and journal exactly.
    for (name, shadowed, shadowing) in undone.into_iter().rev() {
        restore(env, &name, shadowing);
        run.journal.push((name, shadowed));
    }
    r
}

fn walk_bool(
    node: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    if eval_bool(node, env, ctx.defs)? {
        advance(cont, env, ctx, run)
    } else {
        Ok(())
    }
}

fn walk_eq(
    node: &Expr,
    l: &Expr,
    r: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    if let Some((name, keys)) = ctx.assign_target(l) {
        return assign_or_constrain(&name, &keys, r, cont, env, ctx, run);
    }
    if let Some((name, keys)) = ctx.assign_target(r) {
        return assign_or_constrain(&name, &keys, l, cont, env, ctx, run);
    }
    walk_bool(node, cont, env, ctx, run)
}

fn walk_in(
    node: &Expr,
    elem: &Expr,
    set: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    if let Some((name, keys)) = ctx.assign_target(elem)
        && keys.is_empty()
    {
        let key = ctx.key_for(&name);
        if env.get(&key).is_none() {
            let dom = eval_set(set, env, ctx.defs)?;
            for val in dom {
                if ctx.satisfied(run) {
                    break;
                }
                env.insert(key.clone(), val);
                advance(cont, env, ctx, run)?;
            }
            env.remove(&key);
            return Ok(());
        }
    }
    walk_bool(node, cont, env, ctx, run)
}

/// Bind `name'` (possibly at a nested key path) to the value of `rhs`, or, if it
/// is already bound, treat the equality as a constraint.
fn assign_or_constrain(
    name: &Arc<str>,
    keys: &[Expr],
    rhs: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    let key = ctx.key_for(name);
    let rhs_val = eval(rhs, env, ctx.defs)?;

    if keys.is_empty() {
        match env.get(&key).cloned() {
            None => {
                env.insert(key.clone(), rhs_val);
                advance(cont, env, ctx, run)?;
                env.remove(&key);
                Ok(())
            }
            Some(existing) => {
                if existing == rhs_val {
                    advance(cont, env, ctx, run)
                } else {
                    Ok(())
                }
            }
        }
    } else {
        // Indexed assignment `name'[k..] = rhs`. Base is the current binding of
        // `name'` if any, otherwise the pre-state value of `name`. Overwrite
        // semantics; repeated-key constraint handling lands in a later commit.
        let key_vals: Vec<Value> = keys
            .iter()
            .map(|k| eval(k, env, ctx.defs))
            .collect::<Result<_>>()?;
        let base = match env.get(&key).cloned().or_else(|| env.get(name).cloned()) {
            Some(v) => v,
            None => return Ok(()),
        };
        let updated = update_nested_value(&base, &key_vals, rhs_val)?;
        let prev = env.get(&key).cloned();
        env.insert(key.clone(), updated);
        advance(cont, env, ctx, run)?;
        restore(env, &key, prev);
        Ok(())
    }
}

/// Resolve an instance operator to `(merged defs, params, body)`, then
/// substitute the call arguments and walk the body as an action.
fn walk_qualified_call(
    instance_expr: &Expr,
    op: &Arc<str>,
    args: &[Expr],
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    use super::global_state::{PARAMETERIZED_INSTANCES, RESOLVED_INSTANCES};

    let resolved: Option<(Definitions, Vec<Arc<str>>, Expr)> = match instance_expr {
        Expr::Var(instance_name) => RESOLVED_INSTANCES.with(|r| {
            let instances = r.borrow();
            let instance_defs = instances.get(instance_name)?;
            let (params, body) = instance_defs.get(op)?;
            Some((instance_defs.clone(), params.clone(), body.clone()))
        }),
        Expr::FnCall(instance_name, instance_args) => PARAMETERIZED_INSTANCES.with(|r| {
            let instances = r.borrow();
            let param_inst = instances.get(instance_name)?;
            if instance_args.len() != param_inst.params.len() {
                return None;
            }
            let instance_defs =
                super::resolve_parameterized_defs_symbolic(param_inst, instance_args.to_vec());
            let (params, body) = instance_defs.get(op)?;
            let params = params.clone();
            let body = body.clone();
            Some((instance_defs, params, body))
        }),
        _ => None,
    };

    let Some((instance_defs, params, body)) = resolved else {
        // Not resolvable as an action call; fall back to boolean evaluation,
        // which produces the evaluator's own diagnostic.
        let fallback =
            Expr::QualifiedCall(Box::new(instance_expr.clone()), op.clone(), args.to_vec());
        return walk_bool(&fallback, cont, env, ctx, run);
    };

    if params.len() != args.len() {
        let fallback =
            Expr::QualifiedCall(Box::new(instance_expr.clone()), op.clone(), args.to_vec());
        return walk_bool(&fallback, cont, env, ctx, run);
    }

    let subs: Vec<(Arc<str>, Expr)> = params.into_iter().zip(args.iter().cloned()).collect();
    let bound_body = substitute_expr(&body, &subs);

    let mut merged = ctx.defs.clone();
    for (name, def) in instance_defs {
        merged.insert(name, def);
    }
    let sub_ctx = WalkCtx {
        vars: ctx.vars,
        state_keys: ctx.state_keys,
        defs: &merged,
        phase: ctx.phase,
        require_total: ctx.require_total,
    };
    walk(&bound_body, cont, env, &sub_ctx, run)
}

/// If `expr` is a bare state variable, or an indexed access rooted at one,
/// return its base name and key path — the `Init`-phase assignment target.
fn init_target(expr: &Expr, vars: &[Arc<str>]) -> Option<(Arc<str>, Vec<Expr>)> {
    match expr {
        Expr::Var(name) if vars.contains(name) => Some((name.clone(), Vec::new())),
        Expr::FnApp(f, key) => {
            let (name, mut keys) = init_target(f, vars)?;
            keys.push((**key).clone());
            Some((name, keys))
        }
        Expr::RecordAccess(r, field) => {
            let (name, mut keys) = init_target(r, vars)?;
            keys.push(Expr::Lit(Value::Str(field.clone())));
            Some((name, keys))
        }
        Expr::TupleAccess(t, idx) => {
            let (name, mut keys) = init_target(t, vars)?;
            keys.push(Expr::Lit(Value::Int(*idx as i64 + 1)));
            Some((name, keys))
        }
        _ => None,
    }
}

/// If `expr` is a prime, or an indexed access rooted at a prime, return the base
/// variable name and the key path (outermost first).
fn prime_target(expr: &Expr) -> Option<(Arc<str>, Vec<Expr>)> {
    match expr {
        Expr::Prime(name) => Some((name.clone(), Vec::new())),
        Expr::FnApp(f, key) => {
            let (name, mut keys) = prime_target(f)?;
            keys.push((**key).clone());
            Some((name, keys))
        }
        Expr::RecordAccess(r, field) => {
            let (name, mut keys) = prime_target(r)?;
            keys.push(Expr::Lit(Value::Str(field.clone())));
            Some((name, keys))
        }
        Expr::TupleAccess(t, idx) => {
            let (name, mut keys) = prime_target(t)?;
            keys.push(Expr::Lit(Value::Int(*idx as i64 + 1)));
            Some((name, keys))
        }
        _ => None,
    }
}

fn restore(env: &mut Env, key: &Arc<str>, prev: Option<Value>) {
    match prev {
        Some(v) => {
            env.insert(key.clone(), v);
        }
        None => {
            env.remove(key);
        }
    }
}
