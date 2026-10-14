//! Values of constant expressions, computed once per model-checking run.
//!
//! TLC evaluates a constant-level definition once and reuses its value. The parser
//! inlines definitions, so the same applies here to expressions instead: an
//! expression of the spec whose value cannot change during a run (no state
//! variable, prime, bound variable of an enclosing expression, or run-dependent
//! built-in) is evaluated the first time it is needed and kept until the run ends.
//! An evaluation that fails is not kept, so it fails again where it is used.
//!
//! Expressions are identified by address. Only expressions of the spec and of the
//! definitions are registered, and the scope borrows both, so an address cannot be
//! reused by another expression while it is registered.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap};
use std::marker::PhantomData;
use std::sync::Arc;

use super::Definitions;
use super::ast_utils::references_state;
use crate::ast::{Env, Expr, Spec, Value};

type Registry = HashMap<usize, Option<Value>>;

thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static REGISTRY: RefCell<Option<Registry>> = const { RefCell::new(None) };
}

/// Keeps the constant expressions of one run cached until dropped, then restores
/// what was cached before.
pub(crate) struct ConstantCacheScope<'a> {
    previous: Option<Registry>,
    expressions: PhantomData<&'a ()>,
}

impl Drop for ConstantCacheScope<'_> {
    fn drop(&mut self) {
        let previous = self.previous.take();
        ACTIVE.with(|active| active.set(previous.is_some()));
        REGISTRY.with(|registry| *registry.borrow_mut() = previous);
    }
}

/// Caches the constant expressions of `spec` and `defs` while the returned scope
/// lives. `constants` holds the values every expression may read without depending
/// on the state.
pub(crate) fn cache_constant_expressions<'a>(
    spec: &'a Spec,
    defs: &'a Definitions,
    constants: &Env,
) -> ConstantCacheScope<'a> {
    let analysis = Analysis {
        vars: &spec.vars,
        defs,
        constants,
    };
    let mut addresses = Vec::new();
    let mut scope = Vec::new();
    let roots = spec
        .init
        .iter()
        .chain(spec.next.iter())
        .chain(spec.invariants.iter());
    for root in roots {
        analysis.register(root, &mut scope, &mut addresses);
    }
    for (params, body) in defs.values() {
        scope.extend(params.iter().cloned());
        analysis.register(body, &mut scope, &mut addresses);
        scope.clear();
    }
    let registry: Registry = addresses
        .into_iter()
        .map(|address| (address, None))
        .collect();
    ACTIVE.with(|active| active.set(true));
    ConstantCacheScope {
        previous: REGISTRY.with(|current| current.borrow_mut().replace(registry)),
        expressions: PhantomData,
    }
}

pub(super) enum Lookup {
    Cached(Value),
    Registered,
    Unregistered,
}

fn address(expr: &Expr) -> usize {
    std::ptr::from_ref(expr) as usize
}

pub(super) fn lookup(expr: &Expr) -> Lookup {
    if !ACTIVE.with(Cell::get) {
        return Lookup::Unregistered;
    }
    REGISTRY.with(|registry| {
        match registry
            .borrow()
            .as_ref()
            .and_then(|r| r.get(&address(expr)))
        {
            Some(Some(value)) => Lookup::Cached(value.clone()),
            Some(None) => Lookup::Registered,
            None => Lookup::Unregistered,
        }
    })
}

pub(super) fn store(expr: &Expr, value: &Value) {
    REGISTRY.with(|registry| {
        if let Some(slot) = registry
            .borrow_mut()
            .as_mut()
            .and_then(|r| r.get_mut(&address(expr)))
        {
            *slot = Some(value.clone());
        }
    });
}

/// Whether an expression of this kind may be cached: one whose evaluation can be
/// costly. A reference to a zero-parameter definition may be cached too, and is
/// looked up where the evaluator resolves the name.
pub(super) fn is_cacheable(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::SetFilter(..)
            | Expr::SetMap(..)
            | Expr::BigUnion(_)
            | Expr::Powerset(_)
            | Expr::FunctionSet(..)
            | Expr::Cartesian(..)
            | Expr::RecordSet(_)
            | Expr::Union(..)
            | Expr::Intersect(..)
            | Expr::SetMinus(..)
            | Expr::Permutations(_)
            | Expr::Choose(..)
            | Expr::FnDef(..)
            | Expr::FnCall(..)
            | Expr::Forall(..)
            | Expr::Exists(..)
            | Expr::Cardinality(_)
            | Expr::TransitiveClosure(_)
            | Expr::ReflexiveTransitiveClosure(_)
    )
}

struct Analysis<'a> {
    vars: &'a [Arc<str>],
    defs: &'a Definitions,
    constants: &'a Env,
}

/// The names an expression reads that it does not bind itself (`@` among them), and
/// whether it depends on something other than names (a prime, `ENABLED`, an
/// instance, a user-defined infix operator).
struct Free {
    names: BTreeSet<Arc<str>>,
    dynamic: bool,
}

impl Free {
    fn none() -> Self {
        Free {
            names: BTreeSet::new(),
            dynamic: false,
        }
    }

    fn dynamic() -> Self {
        Free {
            names: BTreeSet::new(),
            dynamic: true,
        }
    }

    fn name(name: &Arc<str>) -> Self {
        Free {
            names: BTreeSet::from([name.clone()]),
            dynamic: false,
        }
    }

    fn join(mut self, other: Free) -> Self {
        self.names.extend(other.names);
        self.dynamic |= other.dynamic;
        self
    }

    fn without(mut self, bound: &[Arc<str>]) -> Self {
        for name in bound {
            self.names.remove(name);
        }
        self
    }
}

impl Analysis<'_> {
    /// Registers the outermost cacheable constant subexpressions of `expr`, whose
    /// enclosing expressions bind the names in `scope`, and returns what `expr`
    /// reads.
    fn register(&self, expr: &Expr, scope: &mut Vec<Arc<str>>, out: &mut Vec<usize>) -> Free {
        let start = out.len();
        let free = self.free(expr, scope, out);
        if (is_cacheable(expr) || matches!(expr, Expr::Var(_)))
            && self.is_constant(expr, &free, scope)
        {
            out.truncate(start);
            out.push(address(expr));
        }
        free
    }

    fn is_constant(&self, expr: &Expr, free: &Free, scope: &[Arc<str>]) -> bool {
        if free.dynamic {
            return false;
        }
        let reads_constants = free.names.iter().all(|name| {
            !scope.contains(name)
                && !self.vars.contains(name)
                && (self.constants.contains_key(name) || self.defs.contains_key(name))
        });
        let is_definition = match expr {
            Expr::Var(name) => self.defs.get(name).is_some_and(|(p, _)| p.is_empty()),
            _ => true,
        };
        reads_constants && is_definition && !references_state(expr, self.vars, self.defs)
    }

    fn bind(
        &self,
        bound: &[Arc<str>],
        body: &Expr,
        scope: &mut Vec<Arc<str>>,
        out: &mut Vec<usize>,
    ) -> Free {
        let depth = scope.len();
        scope.extend(bound.iter().cloned());
        let free = self.register(body, scope, out);
        scope.truncate(depth);
        free.without(bound)
    }

    fn all(&self, exprs: &[Expr], scope: &mut Vec<Arc<str>>, out: &mut Vec<usize>) -> Free {
        exprs.iter().fold(Free::none(), |acc, e| {
            acc.join(self.register(e, scope, out))
        })
    }

    fn free(&self, expr: &Expr, scope: &mut Vec<Arc<str>>, out: &mut Vec<usize>) -> Free {
        match expr {
            Expr::Lit(_) | Expr::Any | Expr::EmptyBag => Free::none(),
            Expr::Var(name) => Free::name(name),
            Expr::OldValue => Free::name(&Arc::from("@")),
            Expr::Unparsed(_)
            | Expr::Prime(_)
            | Expr::Unchanged(_)
            | Expr::JavaTime
            | Expr::SystemTime => Free::dynamic(),
            Expr::EnabledOp(e)
            | Expr::RandomElement(e)
            | Expr::TLCGet(e)
            | Expr::Always(e)
            | Expr::Eventually(e) => {
                self.register(e, scope, out);
                Free::dynamic()
            }
            Expr::LeadsTo(l, r)
            | Expr::WeakFairness(l, r)
            | Expr::StrongFairness(l, r)
            | Expr::BoxAction(l, r)
            | Expr::DiamondAction(l, r)
            | Expr::ActionCompose(l, r) => {
                self.register(l, scope, out);
                self.register(r, scope, out);
                Free::dynamic()
            }
            Expr::CustomOp(_, left, right) => {
                self.register(left, scope, out);
                self.register(right, scope, out);
                Free::dynamic()
            }
            Expr::QualifiedCall(instance, _, args) => {
                self.register(instance, scope, out);
                self.all(args, scope, out);
                Free::dynamic()
            }
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
            | Expr::TLCEval(e)
            | Expr::IsABag(e)
            | Expr::BagToSet(e)
            | Expr::SetToBag(e)
            | Expr::BagUnion(e)
            | Expr::SubBag(e)
            | Expr::BagCardinality(e)
            | Expr::RecordAccess(e, _)
            | Expr::TupleAccess(e, _)
            | Expr::LabeledAction(_, e) => self.register(e, scope, out),
            Expr::And(l, r)
            | Expr::Or(l, r)
            | Expr::Implies(l, r)
            | Expr::Equiv(l, r)
            | Expr::Eq(l, r)
            | Expr::Neq(l, r)
            | Expr::In(l, r)
            | Expr::NotIn(l, r)
            | Expr::Add(l, r)
            | Expr::Sub(l, r)
            | Expr::Mul(l, r)
            | Expr::Div(l, r)
            | Expr::Mod(l, r)
            | Expr::Exp(l, r)
            | Expr::BitwiseAnd(l, r)
            | Expr::Lt(l, r)
            | Expr::Le(l, r)
            | Expr::Gt(l, r)
            | Expr::Ge(l, r)
            | Expr::SetRange(l, r)
            | Expr::Union(l, r)
            | Expr::Intersect(l, r)
            | Expr::SetMinus(l, r)
            | Expr::Cartesian(l, r)
            | Expr::Subset(l, r)
            | Expr::ProperSubset(l, r)
            | Expr::FnApp(l, r)
            | Expr::FnMerge(l, r)
            | Expr::SingleFn(l, r)
            | Expr::FunctionSet(l, r)
            | Expr::Append(l, r)
            | Expr::Concat(l, r)
            | Expr::SelectSeq(l, r)
            | Expr::Print(l, r)
            | Expr::Assert(l, r)
            | Expr::SortSeq(l, r)
            | Expr::TLCSet(l, r)
            | Expr::BagIn(l, r)
            | Expr::BagAdd(l, r)
            | Expr::BagSub(l, r)
            | Expr::SqSubseteq(l, r)
            | Expr::BagOfAll(l, r)
            | Expr::CopiesIn(l, r) => {
                let left = self.register(l, scope, out);
                left.join(self.register(r, scope, out))
            }
            Expr::If(a, b, c) | Expr::SubSeq(a, b, c) => {
                let first = self.register(a, scope, out);
                let second = self.register(b, scope, out);
                first.join(second).join(self.register(c, scope, out))
            }
            Expr::SetFilter(var, domain, body)
            | Expr::SetMap(var, domain, body)
            | Expr::Exists(var, domain, body)
            | Expr::Forall(var, domain, body)
            | Expr::Choose(var, domain, body)
            | Expr::FnDef(var, domain, body) => {
                let domain = self.register(domain, scope, out);
                domain.join(self.bind(std::slice::from_ref(var), body, scope, out))
            }
            Expr::ChooseUnbounded(var, body) => {
                self.bind(std::slice::from_ref(var), body, scope, out)
            }
            Expr::Lambda(params, body) => self.bind(params, body, scope, out),
            Expr::Let(var, binding, body) => {
                let binding = self.register(binding, scope, out);
                binding.join(self.bind(std::slice::from_ref(var), body, scope, out))
            }
            Expr::FnCall(name, args) => Free::name(name).join(self.all(args, scope, out)),
            Expr::SetEnum(items) | Expr::TupleLit(items) => self.all(items, scope, out),
            Expr::RecordLit(fields) | Expr::RecordSet(fields) => {
                fields.iter().fold(Free::none(), |acc, (_, e)| {
                    acc.join(self.register(e, scope, out))
                })
            }
            Expr::Except(base, updates) => {
                let mut free = self.register(base, scope, out);
                for (path, value) in updates {
                    free = free.join(self.all(path, scope, out));
                    let at: Arc<str> = Arc::from("@");
                    free = free.join(self.bind(&[at], value, scope, out));
                }
                free
            }
            Expr::Case(arms) => arms.iter().fold(Free::none(), |acc, (guard, value)| {
                let guard = self.register(guard, scope, out);
                acc.join(guard).join(self.register(value, scope, out))
            }),
        }
    }
}
