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
//! The default engine; the legacy candidate-inference engine remains available
//! for one release as an escape hatch (`TLA_ENGINE=inference`).

use std::sync::Arc;

use super::Definitions;
use super::ast_utils::{collect_disjuncts_with_labels, contains_prime_ref};
use super::core::{eval, expand_unchanged_vars};
use super::error::{EvalError, Result};
use super::helpers::{eval_bool, eval_set, get_nested, update_nested_value};
use super::state::env_to_next_state;
use crate::ast::{Env, Expr, Transition, Value};
use crate::intern::primed_name;
use crate::substitution::substitute_expr;

thread_local! {
    static USE_INFERENCE_ENGINE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static ALLOW_UNASSIGNED_STUTTER: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Select the legacy candidate-inference engine instead of the default walker.
/// Retained for one release as an escape hatch (`TLA_ENGINE=inference`).
pub fn set_use_inference_engine(use_inference: bool) {
    USE_INFERENCE_ENGINE.with(|c| c.set(use_inference));
}

/// Whether the walker engine is selected. Default; the inference engine is opt-in.
pub(crate) fn walk_enabled() -> bool {
    !USE_INFERENCE_ENGINE.with(std::cell::Cell::get)
}

/// Opt into treating a variable an action leaves unassigned as an implicit
/// `UNCHANGED` (a stutter of that variable) instead of a hard error. Off by
/// default: an unassigned variable is a malformed action, as in TLC.
pub fn set_allow_unassigned_stutter(allow: bool) {
    ALLOW_UNASSIGNED_STUTTER.with(|c| c.set(allow));
}

fn allow_unassigned_stutter() -> bool {
    ALLOW_UNASSIGNED_STUTTER.with(std::cell::Cell::get)
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
    /// The `(state key, key path)` pairs already assigned on the current branch.
    /// A second assignment to the same path is a *constraint* (compare), not an
    /// overwrite — `f'[1] = 5 /\ f'[1] = 6` is unsatisfiable, and a `\A` that
    /// sets every index must not be silently overwritten by a later `f'[i] = e`.
    assigned_paths: Vec<(Arc<str>, Vec<Value>)>,
    /// State keys bound as a *whole* on this branch (`f' = g`, `f' \in S`, or an
    /// `UNCHANGED f`). A later indexed reference to such a key is a constraint on
    /// the value already there, not an overwrite — `f' = g /\ f'[1] = 5` requires
    /// `g[1] = 5`, it does not rebind index 1 to 5.
    fully_assigned: Vec<Arc<str>>,
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
        assigned_paths: Vec::new(),
        fully_assigned: Vec::new(),
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
            assigned_paths: Vec::new(),
            fully_assigned: Vec::new(),
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
        assigned_paths: Vec::new(),
        fully_assigned: Vec::new(),
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
    if ctx.phase == Phase::Next
        && !matches!(node, Expr::And(_, _))
        && !contains_prime_ref(node, ctx.defs)
        && let Ok(b) = eval_bool(node, env, ctx.defs)
    {
        return if b {
            advance(cont, env, ctx, run)
        } else {
            Ok(())
        };
    }
    match node {
        Expr::And(l, r) => {
            let mark = run.journal.len();
            walk(l, &Cont::Cons(r, mark, cont), env, ctx, run)
        }

        Expr::Or(_, _) if run.action.is_none() => {
            for (disjunct, label) in collect_disjuncts_with_labels(node, ctx.defs) {
                match label {
                    Some(name) => walk_named(name, disjunct, cont, env, ctx, run)?,
                    None => walk(disjunct, cont, env, ctx, run)?,
                }
            }
            Ok(())
        }
        Expr::Or(l, r) => {
            walk(l, cont, env, ctx, run)?;
            walk(r, cont, env, ctx, run)
        }

        Expr::Var(name) => match ctx.defs.get(name) {
            Some((params, body)) if params.is_empty() => {
                walk_named(name.clone(), &body.clone(), cont, env, ctx, run)
            }
            _ => walk_bool(node, cont, env, ctx, run),
        },
        Expr::FnCall(name, args) => match ctx.defs.get(name) {
            Some((params, body)) if params.len() == args.len() => {
                let subs: Vec<(Arc<str>, Expr)> =
                    params.iter().cloned().zip(args.iter().cloned()).collect();
                walk_named(
                    name.clone(),
                    &substitute_expr(body, &subs),
                    cont,
                    env,
                    ctx,
                    run,
                )
            }
            _ => walk_bool(node, cont, env, ctx, run),
        },
        Expr::LabeledAction(label, inner) => walk_named(label.clone(), inner, cont, env, ctx, run),

        Expr::QualifiedCall(instance_expr, op, args) => {
            walk_qualified_call(instance_expr, op, args, cont, env, ctx, run)
        }

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

        Expr::Forall(var, domain, body) => {
            let dom = eval_set(domain, env, ctx.defs)?;
            let items: Vec<Expr> = dom
                .into_iter()
                .map(|val| substitute_expr(body, &[(var.clone(), Expr::Lit(val))]))
                .collect();
            let mark = run.journal.len();
            advance(&Cont::Slice(&items, mark, cont), env, ctx, run)
        }

        Expr::Unchanged(vars) => {
            let items: Vec<Expr> = expand_unchanged_vars(vars, ctx.defs)
                .into_iter()
                .map(|v| Expr::Eq(Box::new(Expr::Prime(v.clone())), Box::new(Expr::Var(v))))
                .collect();
            let mark = run.journal.len();
            advance(&Cont::Slice(&items, mark, cont), env, ctx, run)
        }

        Expr::If(c, t, e) => {
            if eval_bool(c, env, ctx.defs)? {
                walk(t, cont, env, ctx, run)
            } else {
                walk(e, cont, env, ctx, run)
            }
        }

        Expr::Case(branches) => {
            for (guard, body) in branches {
                if eval_bool(guard, env, ctx.defs)? {
                    return walk(body, cont, env, ctx, run);
                }
            }
            Err(EvalError::domain_error("CASE: no matching branch"))
        }

        Expr::Let(name, binding, body) => {
            let bound = substitute_expr(body, &[(name.clone(), (**binding).clone())]);
            walk(&bound, cont, env, ctx, run)
        }

        Expr::Eq(l, r) => walk_eq(node, l, r, cont, env, ctx, run),

        Expr::In(elem, set) => walk_in(node, elem, set, cont, env, ctx, run),

        _ => walk_bool(node, cont, env, ctx, run),
    }
}

/// Walk a named action's body, attributing the successors it emits to `label`
/// unless an enclosing action already claimed them. The label is restored on the
/// way out (including on error) so sibling disjuncts are attributed independently.
/// Matches the inference engine, which labels a transition by the innermost named
/// disjunct that produced it (`sub_action.or(action)`).
fn walk_named(
    label: Arc<str>,
    body: &Expr,
    cont: &Cont<'_>,
    env: &mut Env,
    ctx: &WalkCtx<'_>,
    run: &mut Run<'_>,
) -> Result<()> {
    if run.action.is_some() {
        return walk(body, cont, env, ctx, run);
    }
    run.action = Some(label);
    let result = walk(body, cont, env, ctx, run);
    run.action = None;
    result
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
        Cont::Nil => emit(env, ctx, run),
    }
}

/// Record a successor once the whole relation is discharged. `ENABLED`
/// (`require_total = false`) accepts any partial assignment as a witness.
/// Generating a state (`Next`/`Init`) demands every variable assigned: a
/// variable the action left unbound is a malformed action and a hard error,
/// unless `--allow-unassigned-stutter` opts into treating it as an implicit
/// `UNCHANGED` — only possible in `Next`, where the current value exists.
fn emit(env: &mut Env, ctx: &WalkCtx<'_>, run: &mut Run<'_>) -> Result<()> {
    if !ctx.require_total {
        run.results.push(Transition {
            state: env_to_next_state(env, ctx.vars, ctx.state_keys),
            action: run.action.clone(),
        });
        return Ok(());
    }

    let missing: Vec<usize> = (0..ctx.state_keys.len())
        .filter(|&i| env.get(&ctx.state_keys[i]).is_none())
        .collect();

    if missing.is_empty() {
        run.results.push(Transition {
            state: env_to_next_state(env, ctx.vars, ctx.state_keys),
            action: run.action.clone(),
        });
        return Ok(());
    }

    if ctx.phase == Phase::Next && allow_unassigned_stutter() {
        for &i in &missing {
            if let Some(current) = env.get(&ctx.vars[i]).cloned() {
                env.insert(ctx.state_keys[i].clone(), current);
            }
        }
        if ctx.state_keys.iter().all(|k| env.get(k).is_some()) {
            run.results.push(Transition {
                state: env_to_next_state(env, ctx.vars, ctx.state_keys),
                action: run.action.clone(),
            });
        }
        for &i in &missing {
            env.remove(&ctx.state_keys[i]);
        }
        return Ok(());
    }

    let names = missing
        .iter()
        .map(|&i| ctx.vars[i].to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let action = run
        .action
        .as_ref()
        .map(|a| format!(" in action {a}"))
        .unwrap_or_default();
    Err(EvalError::domain_error(format!(
        "variable(s) not assigned{action}: {names} \
         (pass --allow-unassigned-stutter to treat as UNCHANGED)"
    )))
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
    if run.journal.len() == mark {
        return walk(head, tail, env, ctx, run);
    }

    let mut undone: Vec<(Arc<str>, Option<Value>, Option<Value>)> = Vec::new();
    while run.journal.len() > mark {
        let (name, shadowed) = run.journal.pop().expect("journal longer than mark");
        let shadowing = env.get(&name).cloned();
        restore(env, &name, shadowed.clone());
        undone.push((name, shadowed, shadowing));
    }

    let r = walk(head, tail, env, ctx, run);

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
    if let Some((name, keys)) = ctx.assign_target(elem) {
        if keys.is_empty() {
            let key = ctx.key_for(&name);
            if env.get(&key).is_none() {
                let dom = eval_set(set, env, ctx.defs)?;
                run.fully_assigned.push(key.clone());
                let mut result = Ok(());
                for val in dom {
                    if ctx.satisfied(run) {
                        break;
                    }
                    env.insert(key.clone(), val);
                    result = advance(cont, env, ctx, run);
                    if result.is_err() {
                        break;
                    }
                }
                run.fully_assigned.pop();
                env.remove(&key);
                return result;
            }
        } else {
            let dom = eval_set(set, env, ctx.defs)?;
            let mut result = Ok(());
            for val in dom {
                if ctx.satisfied(run) {
                    break;
                }
                result = assign_or_constrain(&name, &keys, &Expr::Lit(val), cont, env, ctx, run);
                if result.is_err() {
                    break;
                }
            }
            return result;
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
                run.fully_assigned.push(key.clone());
                let r = advance(cont, env, ctx, run);
                run.fully_assigned.pop();
                env.remove(&key);
                r
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
        let key_vals: Vec<Value> = keys
            .iter()
            .map(|k| eval(k, env, ctx.defs))
            .collect::<Result<_>>()?;

        let already_assigned = run.fully_assigned.contains(&key)
            || run
                .assigned_paths
                .iter()
                .any(|(k, p)| *k == key && *p == key_vals);
        if already_assigned {
            let matches = env
                .get(&key)
                .and_then(|v| get_nested(v, &key_vals).ok())
                .is_some_and(|existing| existing == rhs_val);
            return if matches {
                advance(cont, env, ctx, run)
            } else {
                Ok(())
            };
        }

        let base = match env.get(&key).cloned().or_else(|| env.get(name).cloned()) {
            Some(v) => v,
            None => return Ok(()),
        };
        let updated = update_nested_value(&base, &key_vals, rhs_val)?;
        let prev = env.get(&key).cloned();
        env.insert(key.clone(), updated);
        run.assigned_paths.push((key.clone(), key_vals));
        let r = advance(cont, env, ctx, run);
        run.assigned_paths.pop();
        restore(env, &key, prev);
        r
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
        Expr::FnCall(instance_name, instance_args) => {
            let concrete: Option<Vec<Value>> = instance_args
                .iter()
                .map(|a| eval(a, env, ctx.defs).ok())
                .collect();
            PARAMETERIZED_INSTANCES.with(|r| {
                let instances = r.borrow();
                let param_inst = instances.get(instance_name)?;
                if instance_args.len() != param_inst.params.len() {
                    return None;
                }
                let instance_defs = match &concrete {
                    Some(vals) => super::resolve_parameterized_defs(param_inst, vals.clone()),
                    None => super::resolve_parameterized_defs_symbolic(
                        param_inst,
                        instance_args.to_vec(),
                    ),
                };
                let (params, body) = instance_defs.get(op)?;
                let params = params.clone();
                let body = body.clone();
                Some((instance_defs, params, body))
            })
        }
        _ => None,
    };

    let Some((instance_defs, params, body)) = resolved else {
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
