//! Refinement checking: verify `Spec => Alias!Spec` for a non-parameterized
//! `INSTANCE` alias.
//!
//! The abstract module reached through `Alias == INSTANCE M WITH v <- mapping`
//! keeps its `Init`/`Next` as ordinary definitions with the refinement mapping
//! substituted (primes pushed through the mapping too), so `Alias!Init` and
//! `Alias!Next` evaluate directly against a concrete state's environment. This
//! module wires those evaluations into the concrete BFS as a transition
//! invariant: every initial state's abstract image must satisfy the abstract
//! `Init`, and every concrete transition must satisfy the abstract `Next` or
//! leave the abstract image unchanged (a stutter step the abstract spec cannot
//! observe).

use std::sync::Arc;

use crate::ast::{Env, Expr, Spec, State, Value};
use crate::eval::{
    Definitions, EvalError, eval, resolved_instance_def_names, resolved_instance_vars,
};
use crate::intern::primed_name;

/// A module name prefix — an all-uppercase run, or one ending in `_` — as the
/// parser uses to recognise `<Prefix>Init` / `<Prefix>Next`.
fn is_module_prefix(s: &str) -> bool {
    !s.is_empty() && (s.chars().all(|c| c.is_ascii_uppercase()) || s.ends_with('_'))
}

fn is_init_name(name: &str) -> bool {
    name == "Init" || (name.ends_with("Init") && is_module_prefix(&name[..name.len() - 4]))
}

fn is_next_name(name: &str) -> bool {
    name == "Next" || (name.ends_with("Next") && is_module_prefix(&name[..name.len() - 4]))
}

/// Pick the abstract module's `Init`/`Next` operator: prefer the exact canonical
/// name, else the unique `<Prefix>Init`/`<Prefix>Next`. Ambiguity (several
/// matches, none exactly canonical) is an error rather than an alphabetical guess.
fn select_op(
    names: &[Arc<str>],
    canonical: &str,
    is_match: impl Fn(&str) -> bool,
    alias: &Arc<str>,
) -> Result<Arc<str>, String> {
    if let Some(name) = names.iter().find(|n| n.as_ref() == canonical) {
        return Ok(name.clone());
    }
    let mut matches = names.iter().filter(|n| is_match(n));
    match (matches.next(), matches.next()) {
        (Some(only), None) => Ok(only.clone()),
        (None, _) => Err(format!(
            "--check-refinement: the abstract module of `{alias}` has no {canonical} definition"
        )),
        (Some(_), Some(_)) => Err(format!(
            "--check-refinement: the abstract module of `{alias}` has more than one \
             {canonical}-like definition; name the intended one exactly `{canonical}`"
        )),
    }
}

/// A resolved refinement target: the abstract `Init`/`Next` operators reached
/// through `alias`, and the refinement mapping used to detect stutter steps.
///
/// `mapping` covers *every* abstract variable, not only the `WITH` clauses: an
/// abstract variable omitted from `WITH` takes TLA+'s implicit same-name
/// substitution (abstract `v` ← concrete `v`), and a stutter must hold the whole
/// abstract image fixed, so those implicit identity mappings must be compared too.
pub struct RefinementSpec {
    alias: Arc<str>,
    init_name: Arc<str>,
    next_name: Arc<str>,
    mapping: Vec<(Arc<str>, Expr)>,
}

impl RefinementSpec {
    /// Resolve `alias` against the spec's `INSTANCE` declarations and the already
    /// resolved instance definitions. Fails with a user-facing message when the
    /// alias is unknown, parameterized, unresolved, or the abstract module has no
    /// `Init`/`Next`.
    pub fn resolve(alias: &Arc<str>, spec: &Spec) -> Result<Self, String> {
        let instance = spec
            .instances
            .iter()
            .find(|i| i.alias.as_deref() == Some(alias.as_ref()))
            .ok_or_else(|| {
                format!("--check-refinement: no INSTANCE alias `{alias}` in the spec")
            })?;

        if !instance.params.is_empty() {
            return Err(format!(
                "--check-refinement: parameterized instance `{alias}` is not supported"
            ));
        }

        let names = resolved_instance_def_names(alias).ok_or_else(|| {
            format!(
                "--check-refinement: instance `{alias}` was not resolved; \
                 refinement needs a resolvable spec file path (not available in WASM)"
            )
        })?;

        let init_name = select_op(&names, "Init", is_init_name, alias)?;
        let next_name = select_op(&names, "Next", is_next_name, alias)?;

        let abstract_vars = resolved_instance_vars(alias).ok_or_else(|| {
            format!("--check-refinement: the abstract module of `{alias}` has no variables")
        })?;
        let mapping = abstract_vars
            .into_iter()
            .map(|var| {
                let concrete = instance
                    .substitutions
                    .iter()
                    .find(|(name, _)| *name == var)
                    .map(|(_, expr)| expr.clone())
                    .unwrap_or_else(|| Expr::Var(var.clone()));
                (var, concrete)
            })
            .collect();

        Ok(Self {
            alias: alias.clone(),
            init_name,
            next_name,
            mapping,
        })
    }

    pub fn alias(&self) -> Arc<str> {
        self.alias.clone()
    }

    fn qualified(&self, op: &Arc<str>) -> Expr {
        Expr::QualifiedCall(
            Box::new(Expr::Var(self.alias.clone())),
            op.clone(),
            Vec::new(),
        )
    }

    fn state_env(&self, base: &Env, vars: &[Arc<str>], state: &State) -> Env {
        let mut env = base.clone();
        for (i, var) in vars.iter().enumerate() {
            if let Some(value) = state.values.get(i) {
                env.insert(var.clone(), value.clone());
            }
        }
        env
    }

    /// Whether the abstract image of an initial concrete state satisfies the
    /// abstract `Init`.
    pub fn init_holds(
        &self,
        state: &State,
        vars: &[Arc<str>],
        base: &Env,
        defs: &Definitions,
    ) -> Result<bool, EvalError> {
        let mut env = self.state_env(base, vars, state);
        match eval(&self.qualified(&self.init_name), &mut env, defs)? {
            Value::Bool(b) => Ok(b),
            other => Err(EvalError::type_mismatch_ctx(
                "Bool",
                other,
                "refinement Init",
            )),
        }
    }

    /// Whether a concrete transition refines the abstract spec: the abstract
    /// `Next` accepts the mapped transition, or the abstract image is unchanged
    /// (a stutter). `false` is a refinement violation.
    pub fn step_refines(
        &self,
        current: &State,
        successor: &State,
        vars: &[Arc<str>],
        base: &Env,
        defs: &Definitions,
    ) -> Result<bool, EvalError> {
        let mut env = self.state_env(base, vars, current);
        for (i, var) in vars.iter().enumerate() {
            if let Some(value) = successor.values.get(i) {
                env.insert(primed_name(var), value.clone());
            }
        }
        match eval(&self.qualified(&self.next_name), &mut env, defs)? {
            Value::Bool(true) => return Ok(true),
            Value::Bool(false) => {}
            other => {
                return Err(EvalError::type_mismatch_ctx(
                    "Bool",
                    other,
                    "refinement Next",
                ));
            }
        }

        // Stutter: is the abstract image unchanged? `env` already holds the
        // unprimed concrete state (the current state), so the mapping evaluated
        // there is the current abstract image; a fresh env holds the successor.
        let mut successor_env = self.state_env(base, vars, successor);
        for (_abstract_var, mapping) in &self.mapping {
            let before = eval(mapping, &mut env, defs)?;
            let after = eval(mapping, &mut successor_env, defs)?;
            if before != after {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
