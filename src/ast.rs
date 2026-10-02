use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntDomain {
    Nat,
    Int,
}

impl IntDomain {
    pub fn name(self) -> &'static str {
        match self {
            IntDomain::Nat => "Nat",
            IntDomain::Int => "Int",
        }
    }

    pub fn contains(self, n: i64) -> bool {
        match self {
            IntDomain::Nat => n >= 0,
            IntDomain::Int => true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Str(Arc<str>),
    Model(Arc<str>),
    Set(Arc<BTreeSet<Value>>),
    Fn(Arc<BTreeMap<Value, Value>>),
    Record(Arc<BTreeMap<Arc<str>, Value>>),
    Tuple(Arc<Vec<Value>>),
    IntSet(IntDomain),
}

impl Value {
    pub fn set(s: BTreeSet<Value>) -> Self {
        Value::Set(Arc::new(s))
    }

    pub fn func(m: BTreeMap<Value, Value>) -> Self {
        if is_seq_domain(&m) {
            return Value::Tuple(Arc::new(m.into_values().collect()));
        }
        if is_rec_domain(&m) {
            let fields = m
                .into_iter()
                .map(|(k, v)| match k {
                    Value::Str(s) => (s, v),
                    _ => unreachable!("is_rec_domain guarantees every key is Str"),
                })
                .collect();
            return Value::Record(Arc::new(fields));
        }
        Value::Fn(Arc::new(m))
    }

    pub fn record(m: BTreeMap<Arc<str>, Value>) -> Self {
        if m.is_empty() {
            return Value::Tuple(Arc::new(Vec::new()));
        }
        Value::Record(Arc::new(m))
    }

    pub fn tuple(v: Vec<Value>) -> Self {
        Value::Tuple(Arc::new(v))
    }

    pub fn is_function(&self) -> bool {
        matches!(self, Value::Fn(_) | Value::Record(_) | Value::Tuple(_))
    }

    pub fn as_function_map(&self) -> Option<BTreeMap<Value, Value>> {
        match self {
            Value::Fn(f) => Some((**f).clone()),
            Value::Record(r) => Some(
                r.iter()
                    .map(|(k, v)| (Value::Str(k.clone()), v.clone()))
                    .collect(),
            ),
            Value::Tuple(t) => Some(
                t.iter()
                    .enumerate()
                    .map(|(i, v)| (Value::Int(i as i64 + 1), v.clone()))
                    .collect(),
            ),
            _ => None,
        }
    }

    pub fn function_domain(&self) -> Option<BTreeSet<Value>> {
        match self {
            Value::Fn(f) => Some(f.keys().cloned().collect()),
            Value::Record(r) => Some(r.keys().map(|k| Value::Str(k.clone())).collect()),
            Value::Tuple(t) => Some((1..=t.len()).map(|i| Value::Int(i as i64)).collect()),
            _ => None,
        }
    }
}

fn is_seq_domain(m: &BTreeMap<Value, Value>) -> bool {
    let n = m.len();
    if n == 0 {
        return true;
    }
    matches!(m.keys().next(), Some(Value::Int(1)))
        && matches!(m.keys().next_back(), Some(Value::Int(k)) if *k == n as i64)
}

fn is_rec_domain(m: &BTreeMap<Value, Value>) -> bool {
    !m.is_empty()
        && matches!(m.keys().next(), Some(Value::Str(_)))
        && matches!(m.keys().next_back(), Some(Value::Str(_)))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Lit(Value),
    Var(Arc<str>),
    Prime(Arc<str>),
    OldValue,

    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Implies(Box<Expr>, Box<Expr>),
    Equiv(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Neq(Box<Expr>, Box<Expr>),
    In(Box<Expr>, Box<Expr>),
    NotIn(Box<Expr>, Box<Expr>),

    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Exp(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    BitwiseAnd(Box<Expr>, Box<Expr>),
    TransitiveClosure(Box<Expr>),
    ReflexiveTransitiveClosure(Box<Expr>),
    ActionCompose(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),

    SetEnum(Vec<Expr>),
    SetRange(Box<Expr>, Box<Expr>),
    SetFilter(Arc<str>, Box<Expr>, Box<Expr>),
    SetMap(Arc<str>, Box<Expr>, Box<Expr>),
    Union(Box<Expr>, Box<Expr>),
    Intersect(Box<Expr>, Box<Expr>),
    SetMinus(Box<Expr>, Box<Expr>),
    Cartesian(Box<Expr>, Box<Expr>),
    Subset(Box<Expr>, Box<Expr>),
    ProperSubset(Box<Expr>, Box<Expr>),
    Powerset(Box<Expr>),
    Cardinality(Box<Expr>),
    IsFiniteSet(Box<Expr>),
    BigUnion(Box<Expr>),

    Exists(Arc<str>, Box<Expr>, Box<Expr>),
    Forall(Arc<str>, Box<Expr>, Box<Expr>),
    Choose(Arc<str>, Box<Expr>, Box<Expr>),
    ChooseUnbounded(Arc<str>, Box<Expr>),

    FnApp(Box<Expr>, Box<Expr>),
    FnDef(Arc<str>, Box<Expr>, Box<Expr>),
    FnCall(Arc<str>, Vec<Expr>),
    Lambda(Vec<Arc<str>>, Box<Expr>),
    FnMerge(Box<Expr>, Box<Expr>),
    SingleFn(Box<Expr>, Box<Expr>),
    CustomOp(Arc<str>, Box<Expr>, Box<Expr>),
    Except(Box<Expr>, Vec<(Vec<Expr>, Expr)>),
    Domain(Box<Expr>),
    FunctionSet(Box<Expr>, Box<Expr>),

    RecordLit(Vec<(Arc<str>, Expr)>),
    RecordSet(Vec<(Arc<str>, Expr)>),
    RecordAccess(Box<Expr>, Arc<str>),

    TupleLit(Vec<Expr>),
    TupleAccess(Box<Expr>, usize),

    Len(Box<Expr>),
    Head(Box<Expr>),
    Tail(Box<Expr>),
    Append(Box<Expr>, Box<Expr>),
    Concat(Box<Expr>, Box<Expr>),
    SubSeq(Box<Expr>, Box<Expr>, Box<Expr>),
    SelectSeq(Box<Expr>, Box<Expr>),
    SeqSet(Box<Expr>),
    Print(Box<Expr>, Box<Expr>),
    PrintT(Box<Expr>),
    Assert(Box<Expr>, Box<Expr>),
    JavaTime,
    SystemTime,
    Permutations(Box<Expr>),
    SortSeq(Box<Expr>, Box<Expr>),
    TLCToString(Box<Expr>),
    RandomElement(Box<Expr>),
    TLCGet(Box<Expr>),
    TLCSet(Box<Expr>, Box<Expr>),
    Any,
    TLCEval(Box<Expr>),

    IsABag(Box<Expr>),
    BagToSet(Box<Expr>),
    SetToBag(Box<Expr>),
    BagIn(Box<Expr>, Box<Expr>),
    EmptyBag,
    BagAdd(Box<Expr>, Box<Expr>),
    BagSub(Box<Expr>, Box<Expr>),
    BagUnion(Box<Expr>),
    SqSubseteq(Box<Expr>, Box<Expr>),
    SubBag(Box<Expr>),
    BagOfAll(Box<Expr>, Box<Expr>),
    BagCardinality(Box<Expr>),
    CopiesIn(Box<Expr>, Box<Expr>),

    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Arc<str>, Box<Expr>, Box<Expr>),
    Case(Vec<(Expr, Expr)>),

    Unchanged(Vec<Arc<str>>),

    Always(Box<Expr>),
    Eventually(Box<Expr>),
    LeadsTo(Box<Expr>, Box<Expr>),
    WeakFairness(Box<Expr>, Box<Expr>),
    StrongFairness(Box<Expr>, Box<Expr>),
    BoxAction(Box<Expr>, Box<Expr>),
    DiamondAction(Box<Expr>, Box<Expr>),
    EnabledOp(Box<Expr>),

    QualifiedCall(Box<Expr>, Arc<str>, Vec<Expr>),

    LabeledAction(Arc<str>, Box<Expr>),
}

#[derive(Clone, Debug)]
pub struct Env {
    entries: Vec<(Arc<str>, Value)>,
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            entries: Vec::with_capacity(cap),
        }
    }

    pub fn get(&self, key: &Arc<str>) -> Option<&Value> {
        let ptr = Arc::as_ptr(key);
        for (k, v) in &self.entries {
            if std::ptr::addr_eq(Arc::as_ptr(k), ptr) || **k == **key {
                return Some(v);
            }
        }
        None
    }

    pub fn insert(&mut self, key: Arc<str>, value: Value) -> Option<Value> {
        let ptr = Arc::as_ptr(&key);
        for (k, v) in &mut self.entries {
            if std::ptr::addr_eq(Arc::as_ptr(k), ptr) || **k == *key {
                return Some(std::mem::replace(v, value));
            }
        }
        self.entries.push((key, value));
        None
    }

    pub fn remove(&mut self, key: &Arc<str>) -> Option<Value> {
        let ptr = Arc::as_ptr(key);
        for i in 0..self.entries.len() {
            if std::ptr::addr_eq(Arc::as_ptr(&self.entries[i].0), ptr)
                || *self.entries[i].0 == **key
            {
                return Some(self.entries.remove(i).1);
            }
        }
        None
    }

    pub fn contains_key(&self, key: &Arc<str>) -> bool {
        let ptr = Arc::as_ptr(key);
        self.entries
            .iter()
            .any(|(k, _)| std::ptr::addr_eq(Arc::as_ptr(k), ptr) || **k == **key)
    }

    pub fn keys(&self) -> impl Iterator<Item = &Arc<str>> {
        self.entries.iter().map(|(k, _)| k)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Arc<str>, &Value)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }
}

impl<'a> IntoIterator for &'a Env {
    type Item = (&'a Arc<str>, &'a Value);
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, (Arc<str>, Value)>,
        fn(&'a (Arc<str>, Value)) -> (&'a Arc<str>, &'a Value),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter().map(|(k, v)| (k, v))
    }
}

impl IntoIterator for Env {
    type Item = (Arc<str>, Value);
    type IntoIter = std::vec::IntoIter<(Arc<str>, Value)>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl FromIterator<(Arc<str>, Value)> for Env {
    fn from_iter<I: IntoIterator<Item = (Arc<str>, Value)>>(iter: I) -> Self {
        let entries: Vec<(Arc<str>, Value)> = iter.into_iter().collect();
        debug_assert!(
            {
                let mut seen = std::collections::HashSet::new();
                entries.iter().all(|(k, _)| seen.insert(&**k))
            },
            "Env::from_iter called with duplicate keys"
        );
        Self { entries }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    pub values: Vec<Value>,
}

#[derive(Debug, Clone)]
pub struct InstanceDecl {
    pub alias: Option<Arc<str>>,
    pub params: Vec<Arc<str>>,
    pub module_name: Arc<str>,
    pub substitutions: Vec<(Arc<str>, Expr)>,
}

#[derive(Debug, Clone)]
pub enum FairnessConstraint {
    Weak(Expr, Expr),
    Strong(Expr, Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition {
    pub state: State,
    pub action: Option<Arc<str>>,
}

pub type DefinitionMap = BTreeMap<Arc<str>, (Vec<Arc<str>>, Arc<Expr>)>;

/// A liveness obligation named after the definition it came from: a cfg `PROPERTY`,
/// or (legacy, without a cfg that defines the behavior) a `*Spec` definition whose
/// temporal conjuncts are checked instead of assumed.
#[derive(Debug, Clone)]
pub struct LivenessProperty {
    pub name: Arc<str>,
    pub formula: Expr,
    pub from_specification: bool,
}

/// The non-liveness parts of a cfg `PROPERTY`, checked during the safety search as
/// TLC does: a state predicate on the initial states, and `[][A]_v` on every
/// transition. A `[]P` conjunct is added to the invariants instead.
#[derive(Debug, Clone)]
pub enum SafetyProperty {
    Init { name: Arc<str>, predicate: Expr },
    Action { name: Arc<str>, formula: Expr },
}

impl SafetyProperty {
    pub fn name(&self) -> &Arc<str> {
        match self {
            SafetyProperty::Init { name, .. } | SafetyProperty::Action { name, .. } => name,
        }
    }
}

pub struct Spec {
    pub vars: Vec<Arc<str>>,
    pub constants: Vec<Arc<str>>,
    pub extends: Vec<Arc<str>>,
    pub definitions: DefinitionMap,
    pub assumes: Vec<Expr>,
    pub instances: Vec<InstanceDecl>,
    pub init: Option<Expr>,
    pub next: Option<Expr>,
    pub invariants: Vec<Expr>,
    pub invariant_names: Vec<Option<Arc<str>>>,
    pub fairness: Vec<FairnessConstraint>,
    pub quantified_fairness: Vec<(Arc<str>, Expr, Expr)>,
    pub liveness_properties: Vec<LivenessProperty>,
    pub safety_properties: Vec<SafetyProperty>,
    /// The cfg `SPECIFICATION`'s temporal conjuncts other than `WF`/`SF`, which TLC
    /// treats as assumptions: only behaviors satisfying them are checked.
    pub temporal_assumptions: Vec<Expr>,
}

/// `[](P => <>Q)` with `P` and `Q` free of temporal operators, which is exactly
/// `P ~> Q`. Any other shape under `[]` is left alone so it is never mistaken for a
/// leads-to property.
pub fn leads_to_form(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Always(inner) = expr else {
        return None;
    };
    let Expr::Implies(p, rhs) = inner.as_ref() else {
        return None;
    };
    let Expr::Eventually(q) = rhs.as_ref() else {
        return None;
    };
    (is_state_level(p) && is_state_level(q)).then_some((p.as_ref(), q.as_ref()))
}

pub fn expr_contains_temporal(expr: &Expr) -> bool {
    if leads_to_form(expr).is_some() {
        return true;
    }
    match expr {
        Expr::WeakFairness(_, _)
        | Expr::StrongFairness(_, _)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::DiamondAction(_, _) => true,
        Expr::And(l, r) | Expr::Or(l, r) => expr_contains_temporal(l) || expr_contains_temporal(r),
        Expr::Always(inner) => expr_contains_temporal(inner),
        Expr::Forall(_, _, body) | Expr::Exists(_, _, body) => expr_contains_temporal(body),
        _ => false,
    }
}

/// Collect the temporal conjuncts of a specification body: fairness into
/// `fairness`, other temporal formulas into `liveness`. A `\A x \in S : body` goes
/// to `quantified` when its body holds fairness and to `liveness` (whole) when its
/// body holds other temporal formulas; each consumer takes only its own kind when
/// the quantifier is expanded.
pub fn collect_temporal(
    expr: &Expr,
    fairness: &mut Vec<FairnessConstraint>,
    liveness: &mut Vec<Expr>,
    quantified: &mut Vec<(Arc<str>, Expr, Expr)>,
    warnings: &mut Vec<String>,
) {
    match expr {
        Expr::WeakFairness(subscript, action) => {
            fairness.push(FairnessConstraint::Weak(
                (**subscript).clone(),
                (**action).clone(),
            ));
        }
        Expr::StrongFairness(subscript, action) => {
            fairness.push(FairnessConstraint::Strong(
                (**subscript).clone(),
                (**action).clone(),
            ));
        }
        Expr::Eventually(inner) => {
            liveness.push(Expr::Eventually(inner.clone()));
        }
        Expr::LeadsTo(p, q) => {
            liveness.push(Expr::LeadsTo(p.clone(), q.clone()));
        }
        Expr::And(l, r) | Expr::Or(l, r) => {
            collect_temporal(l, fairness, liveness, quantified, warnings);
            collect_temporal(r, fairness, liveness, quantified, warnings);
        }
        Expr::Always(inner) => {
            if let Some((p, q)) = leads_to_form(expr) {
                liveness.push(Expr::LeadsTo(Box::new(p.clone()), Box::new(q.clone())));
            } else if let Expr::Eventually(p) = inner.as_ref() {
                liveness.push((**p).clone());
            } else {
                collect_temporal(inner, fairness, liveness, quantified, warnings);
            }
        }
        Expr::BoxAction(inner, _) => {
            collect_temporal(inner, fairness, liveness, quantified, warnings);
        }
        Expr::Forall(var, domain, body) if expr_contains_temporal(body) => {
            let mut body_fairness = Vec::new();
            let mut body_liveness = Vec::new();
            let mut body_quantified = Vec::new();
            collect_temporal(
                body,
                &mut body_fairness,
                &mut body_liveness,
                &mut body_quantified,
                warnings,
            );
            if !body_fairness.is_empty() || !body_quantified.is_empty() {
                quantified.push((var.clone(), (**domain).clone(), (**body).clone()));
            }
            if !body_liveness.is_empty() {
                liveness.push(expr.clone());
            }
        }
        Expr::Exists(var, domain, body) if expr_contains_temporal(body) => {
            match distribute_exists(var, domain, body) {
                Some(property) => liveness.push(property),
                None => warnings.push(
                    "existential temporal property \\E x \\in S : P is only supported when P is <>Q or []<>Q — dropping".to_string(),
                ),
            }
        }
        Expr::DiamondAction(_, _) => {
            warnings.push(
                "temporal operator <<A>>_v (diamond action) is not currently extracted into fairness or liveness — dropping".to_string(),
            );
        }
        _ => {}
    }
}

/// `\E x \in S : <>Q(x)` is `<>(\E x \in S : Q(x))` and `\E x \in S : []<>Q(x)` is
/// `[]<>(\E x \in S : Q(x))`, because `<>` and `[]<>` distribute over disjunction.
/// No other temporal body distributes, so those return `None`.
fn distribute_exists(var: &Arc<str>, domain: &Expr, body: &Expr) -> Option<Expr> {
    let exists = |inner: &Expr| {
        Expr::Exists(
            var.clone(),
            Box::new(domain.clone()),
            Box::new(inner.clone()),
        )
    };
    match body {
        Expr::Eventually(inner) if is_state_level(inner) => {
            Some(Expr::Eventually(Box::new(exists(inner))))
        }
        Expr::Always(inner) => match inner.as_ref() {
            Expr::Eventually(p) if is_state_level(p) => Some(exists(p)),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn has_temporal_operator(expr: &Expr) -> bool {
    match expr {
        Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFairness(_, _)
        | Expr::StrongFairness(_, _)
        | Expr::BoxAction(_, _)
        | Expr::DiamondAction(_, _) => true,
        Expr::And(l, r) | Expr::Or(l, r) | Expr::Implies(l, r) | Expr::Equiv(l, r) => {
            has_temporal_operator(l) || has_temporal_operator(r)
        }
        Expr::Not(e) | Expr::LabeledAction(_, e) => has_temporal_operator(e),
        Expr::If(c, t, e) => {
            has_temporal_operator(c) || has_temporal_operator(t) || has_temporal_operator(e)
        }
        Expr::Forall(_, _, body) | Expr::Exists(_, _, body) => has_temporal_operator(body),
        Expr::Let(_, binding, body) => {
            has_temporal_operator(body)
                || (crate::eval::parameterized_let_op(binding).is_none()
                    && has_temporal_operator(binding))
        }
        _ => false,
    }
}

fn is_state_level(expr: &Expr) -> bool {
    !has_temporal_operator(expr)
}

/// The formula without its `WF`/`SF` conjuncts (including quantified ones), or `None`
/// when nothing else is left.
pub fn without_fairness(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::WeakFairness(_, _) | Expr::StrongFairness(_, _) => None,
        Expr::And(l, r) => match (without_fairness(l), without_fairness(r)) {
            (Some(l), Some(r)) => Some(Expr::And(Box::new(l), Box::new(r))),
            (one, None) | (None, one) => one,
        },
        Expr::Forall(var, domain, body) => without_fairness(body)
            .map(|body| Expr::Forall(var.clone(), domain.clone(), Box::new(body))),
        other => Some(other.clone()),
    }
}

/// One conjunct of a cfg `PROPERTY`, classified as TLC does (`processConfigProps`).
#[derive(Debug, Clone)]
pub enum PropertyPart {
    /// A state predicate: checked on the initial states only.
    Init(Expr),
    /// `[]P` with `P` a state predicate: an invariant.
    Invariant(Expr),
    /// `[][A]_v`, possibly under `\A x \in S`: every transition is an `A` step or
    /// leaves `v` unchanged, for every instance.
    Action(Expr),
    /// Everything else: in the form `liveness::find_violation` checks, or as written
    /// for the tableau checker.
    Liveness(Expr),
}

/// Split a cfg `PROPERTY` into what is checked and how. Every conjunct is an
/// obligation, so a shape the checker cannot represent is an error: in a
/// `SPECIFICATION` body a dropped conjunct only weakens an assumption, but in a
/// property it would silently report the missing obligation as satisfied.
/// A disjunction of liveness properties is checked as the conjunction of its
/// disjuncts, which can only report a violation that does not exist, never miss one
/// that does; any other disjunction with a temporal disjunct is rejected, since
/// splitting it would turn a state predicate or `[]P` into a hard obligation.
///
/// With [`Classification::Syntactic`] the property is classified as TLC does, on its
/// syntax once operators are expanded: only a state predicate, `[]P` and `[][A]_v`
/// are safety parts, and every other conjunct, whatever its shape, is passed whole
/// to the tableau checker.
pub fn classify_property(
    expr: &Expr,
    vars: &[Arc<str>],
    defs: &DefinitionMap,
    mode: Classification,
) -> Result<Vec<PropertyPart>, String> {
    let normalizer = Normalizer { vars, defs, mode };
    let normalized = normalizer.normalize(expr, &[], &mut Vec::new(), 0);
    normalizer.require_constant_domains(&normalized)?;
    let mut parts = Vec::new();
    classify_into(&normalized, mode, &mut parts)?;
    Ok(parts)
}

/// `expr` with the operators and `LET` definitions whose bodies are temporal expanded
/// in place, and nothing else rewritten.
pub fn inline_temporal_definitions(expr: &Expr, vars: &[Arc<str>], defs: &DefinitionMap) -> Expr {
    let normalizer = Normalizer {
        vars,
        defs,
        mode: Classification::Syntactic,
    };
    normalizer.normalize(expr, &[], &mut Vec::new(), 0)
}

/// How a `PROPERTY` is classified: rewritten into the shapes the property-shape
/// checker supports, or taken as written for the tableau checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Classification {
    Rewriting,
    Syntactic,
}

/// How deep operator definitions are inlined while looking for temporal operators;
/// a recursive operator stops being expanded there and is left as a call.
const MAX_INLINE_DEPTH: usize = 32;

type LocalOperator = (Arc<str>, Vec<Arc<str>>, Expr);

/// Rewrites a property into the shapes `classify_into` understands, preserving its
/// meaning: operators and `LET` definitions whose bodies are temporal are inlined,
/// `[][]P` and `<><>P` collapse, negation is pushed through `[]`, `<>`, `/\`, `\/`,
/// `=>` and quantifiers, and an antecedent (or `IF` condition) that refers to no
/// state variable is pushed inside the temporal operators it guards.
/// With [`Classification::Syntactic`] only operators and `LET` definitions are
/// expanded.
struct Normalizer<'a> {
    vars: &'a [Arc<str>],
    defs: &'a DefinitionMap,
    mode: Classification,
}

impl Normalizer<'_> {
    fn normalize(
        &self,
        expr: &Expr,
        locals: &[LocalOperator],
        bound: &mut Vec<Arc<str>>,
        depth: usize,
    ) -> Expr {
        let recurse = |e: &Expr, bound: &mut Vec<Arc<str>>| self.normalize(e, locals, bound, depth);
        if self.mode == Classification::Syntactic {
            let rebuilt = match expr {
                Expr::Implies(l, r) => Some(Expr::Implies(
                    Box::new(recurse(l, bound)),
                    Box::new(recurse(r, bound)),
                )),
                Expr::Not(inner) => Some(Expr::Not(Box::new(recurse(inner, bound)))),
                Expr::If(cond, then_branch, else_branch) => Some(Expr::If(
                    Box::new(recurse(cond, bound)),
                    Box::new(recurse(then_branch, bound)),
                    Box::new(recurse(else_branch, bound)),
                )),
                Expr::Always(inner) => Some(Expr::Always(Box::new(recurse(inner, bound)))),
                Expr::Eventually(inner) => Some(Expr::Eventually(Box::new(recurse(inner, bound)))),
                _ => None,
            };
            if let Some(rebuilt) = rebuilt {
                return rebuilt;
            }
        }
        match expr {
            Expr::And(l, r) => Expr::And(Box::new(recurse(l, bound)), Box::new(recurse(r, bound))),
            Expr::Or(l, r) => Expr::Or(Box::new(recurse(l, bound)), Box::new(recurse(r, bound))),
            Expr::Implies(l, r) => {
                let (guard, body) = (recurse(l, bound), recurse(r, bound));
                self.guarded(guard, body)
            }
            Expr::Not(inner) => {
                if let Expr::If(cond, then_branch, else_branch) = inner.as_ref()
                    && !self.refers_to_state(cond)
                {
                    let branches = Expr::If(
                        cond.clone(),
                        Box::new(Expr::Not(then_branch.clone())),
                        Box::new(Expr::Not(else_branch.clone())),
                    );
                    return recurse(&branches, bound);
                }
                let inner = recurse(inner, bound);
                if has_temporal_operator(&inner) {
                    negate(inner)
                } else {
                    Expr::Not(Box::new(inner))
                }
            }
            Expr::If(cond, then_branch, else_branch) => {
                let (then_branch, else_branch) =
                    (recurse(then_branch, bound), recurse(else_branch, bound));
                if !has_temporal_operator(&then_branch) && !has_temporal_operator(&else_branch) {
                    return expr.clone();
                }
                let cond = recurse(cond, bound);
                if self.refers_to_state(&cond) {
                    return Expr::If(Box::new(cond), Box::new(then_branch), Box::new(else_branch));
                }
                Expr::And(
                    Box::new(self.guarded(cond.clone(), then_branch)),
                    Box::new(self.guarded(Expr::Not(Box::new(cond)), else_branch)),
                )
            }
            Expr::Always(inner) => always(recurse(inner, bound)),
            Expr::Eventually(inner) => eventually(recurse(inner, bound)),
            Expr::LeadsTo(l, r) => {
                Expr::LeadsTo(Box::new(recurse(l, bound)), Box::new(recurse(r, bound)))
            }
            Expr::Forall(var, domain, body) | Expr::Exists(var, domain, body) => {
                bound.push(var.clone());
                let body = recurse(body, bound);
                bound.pop();
                let rebuilt = |b: Expr| match expr {
                    Expr::Forall(..) => Expr::Forall(var.clone(), domain.clone(), Box::new(b)),
                    _ => Expr::Exists(var.clone(), domain.clone(), Box::new(b)),
                };
                rebuilt(body)
            }
            Expr::Let(name, binding, body) => {
                let inlined = match crate::eval::parameterized_let_op(binding) {
                    Some((params, op_body)) => {
                        let mut scope = locals.to_vec();
                        scope.push((name.clone(), params, op_body.clone()));
                        let inlined = self.normalize(body, &scope, bound, depth);
                        let rebind =
                            |leaf: Expr| Expr::Let(name.clone(), binding.clone(), Box::new(leaf));
                        wrap_non_temporal(inlined, &rebind)
                    }
                    None if crate::eval::reaches_temporal(body, self.defs)
                        || crate::eval::reaches_temporal(binding, self.defs) =>
                    {
                        let subs = [(name.clone(), (**binding).clone())];
                        let body = crate::substitution::substitute_expr(body, &subs);
                        self.normalize(&body, locals, bound, depth)
                    }
                    None => return expr.clone(),
                };
                if has_temporal_operator(&inlined) {
                    inlined
                } else {
                    expr.clone()
                }
            }
            Expr::Var(name) if !bound.contains(name) => {
                self.inline(expr, name, &[], locals, bound, depth)
            }
            Expr::FnCall(name, args) if !bound.contains(name) => {
                self.inline(expr, name, args, locals, bound, depth)
            }
            _ => expr.clone(),
        }
    }

    /// The body of the operator `name` applied to `args`, when that body is
    /// temporal; otherwise the call is left for the evaluator.
    fn inline(
        &self,
        call: &Expr,
        name: &Arc<str>,
        args: &[Expr],
        locals: &[LocalOperator],
        bound: &mut Vec<Arc<str>>,
        depth: usize,
    ) -> Expr {
        if depth >= MAX_INLINE_DEPTH {
            return call.clone();
        }
        let local = locals.iter().rev().find(|(n, _, _)| n == name);
        let (params, body) = match local {
            Some((_, params, body)) => (params.clone(), body.clone()),
            None => match self.defs.get(name) {
                Some((params, body)) => (params.clone(), (**body).clone()),
                None => return call.clone(),
            },
        };
        if params.len() != args.len()
            || (local.is_none() && !crate::eval::reaches_temporal(&body, self.defs))
        {
            return call.clone();
        }
        let subs: Vec<(Arc<str>, Expr)> = params.into_iter().zip(args.iter().cloned()).collect();
        let body = crate::substitution::substitute_expr(&body, &subs);
        let inlined = self.normalize(&body, locals, bound, depth + 1);
        if local.is_some() || has_temporal_operator(&inlined) {
            inlined
        } else {
            call.clone()
        }
    }

    /// A quantifier around a temporal formula ranges over a set fixed at the start
    /// of the behavior; TLC rejects one whose set depends on the state, and checking
    /// it per state would give a different formula, so it is rejected here too.
    fn require_constant_domains(&self, expr: &Expr) -> Result<(), String> {
        if !has_temporal_operator(expr) {
            return Ok(());
        }
        match expr {
            Expr::Forall(var, domain, body) | Expr::Exists(var, domain, body) => {
                if self.refers_to_state(domain) {
                    return Err(format!(
                        "a quantifier `{var} \\in ..` around a temporal formula must range over a \
                         set that does not depend on the state"
                    ));
                }
                self.require_constant_domains(body)
            }
            Expr::And(l, r)
            | Expr::Or(l, r)
            | Expr::Implies(l, r)
            | Expr::Equiv(l, r)
            | Expr::LeadsTo(l, r) => {
                self.require_constant_domains(l)?;
                self.require_constant_domains(r)
            }
            Expr::Always(e) | Expr::Eventually(e) | Expr::Not(e) => {
                self.require_constant_domains(e)
            }
            Expr::If(c, t, e) => {
                self.require_constant_domains(c)?;
                self.require_constant_domains(t)?;
                self.require_constant_domains(e)
            }
            _ => Ok(()),
        }
    }

    fn refers_to_state(&self, expr: &Expr) -> bool {
        crate::eval::references_state(expr, self.vars, self.defs)
    }

    /// `guard => body`, with a guard that refers to no state variable pushed inside
    /// the temporal operators of `body` (it has the same value in every state).
    fn guarded(&self, guard: Expr, body: Expr) -> Expr {
        let implies = |g: Expr, b: Expr| Expr::Implies(Box::new(g), Box::new(b));
        if !has_temporal_operator(&body)
            || has_temporal_operator(&guard)
            || self.refers_to_state(&guard)
        {
            return implies(guard, body);
        }
        push_guard(&guard, &body).unwrap_or_else(|| implies(guard, body))
    }
}

/// `expr` with `wrap` applied to each maximal subformula free of temporal operators
/// (state predicates, actions and subscripts), leaving the temporal structure intact.
fn wrap_non_temporal(expr: Expr, wrap: &dyn Fn(Expr) -> Expr) -> Expr {
    if !has_temporal_operator(&expr) {
        return wrap(expr);
    }
    let go = |e: Box<Expr>| Box::new(wrap_non_temporal(*e, wrap));
    match expr {
        Expr::Always(e) => Expr::Always(go(e)),
        Expr::Eventually(e) => Expr::Eventually(go(e)),
        Expr::Not(e) => Expr::Not(go(e)),
        Expr::And(l, r) => Expr::And(go(l), go(r)),
        Expr::Or(l, r) => Expr::Or(go(l), go(r)),
        Expr::Implies(l, r) => Expr::Implies(go(l), go(r)),
        Expr::Equiv(l, r) => Expr::Equiv(go(l), go(r)),
        Expr::LeadsTo(l, r) => Expr::LeadsTo(go(l), go(r)),
        Expr::If(c, t, e) => Expr::If(go(c), go(t), go(e)),
        Expr::Forall(v, d, b) => Expr::Forall(v, go(d), go(b)),
        Expr::Exists(v, d, b) => Expr::Exists(v, go(d), go(b)),
        Expr::BoxAction(a, v) => Expr::BoxAction(go(a), go(v)),
        Expr::DiamondAction(a, v) => Expr::DiamondAction(go(a), go(v)),
        Expr::WeakFairness(v, a) => Expr::WeakFairness(go(v), go(a)),
        Expr::StrongFairness(v, a) => Expr::StrongFairness(go(v), go(a)),
        other => other,
    }
}

fn always(inner: Expr) -> Expr {
    match inner {
        Expr::Always(_) => inner,
        other => Expr::Always(Box::new(other)),
    }
}

fn eventually(inner: Expr) -> Expr {
    match inner {
        Expr::Eventually(_) => inner,
        other => Expr::Eventually(Box::new(other)),
    }
}

/// `~expr` for a normalized temporal `expr`, pushed inward as far as the operators
/// allow; what cannot be pushed through stays under `~`.
fn negate(expr: Expr) -> Expr {
    let not = |e: Expr| {
        if has_temporal_operator(&e) {
            negate(e)
        } else {
            Expr::Not(Box::new(e))
        }
    };
    match expr {
        Expr::Not(inner) => *inner,
        Expr::Always(inner) => eventually(not(*inner)),
        Expr::Eventually(inner) => always(not(*inner)),
        Expr::And(l, r) => Expr::Or(Box::new(not(*l)), Box::new(not(*r))),
        Expr::Or(l, r) => Expr::And(Box::new(not(*l)), Box::new(not(*r))),
        Expr::Implies(l, r) => Expr::And(l, Box::new(not(*r))),
        Expr::Forall(var, domain, body) => Expr::Exists(var, domain, Box::new(not(*body))),
        Expr::Exists(var, domain, body) => Expr::Forall(var, domain, Box::new(not(*body))),
        other => Expr::Not(Box::new(other)),
    }
}

/// `guard => body` rewritten so the guard sits under the temporal operators, valid
/// because the guard has the same value in every state. `None` when `body` has a
/// shape the guard cannot be pushed into.
fn push_guard(guard: &Expr, body: &Expr) -> Option<Expr> {
    let implies = |b: &Expr| Expr::Implies(Box::new(guard.clone()), Box::new(b.clone()));
    let and_guard = |b: &Expr| Expr::And(Box::new(guard.clone()), Box::new(b.clone()));
    if is_state_level(body) {
        return Some(implies(body));
    }
    if let Some((p, q)) = leads_to_form(body) {
        return Some(Expr::LeadsTo(Box::new(and_guard(p)), Box::new(q.clone())));
    }
    match body {
        Expr::And(l, r) => Some(Expr::And(
            Box::new(push_guard(guard, l)?),
            Box::new(push_guard(guard, r)?),
        )),
        Expr::Or(l, r) => Some(Expr::Or(
            Box::new(push_guard(guard, l)?),
            Box::new(push_guard(guard, r)?),
        )),
        Expr::Always(inner) => match inner.as_ref() {
            Expr::Eventually(p) if is_state_level(p) => Some(always(eventually(implies(p)))),
            p if is_state_level(p) => Some(always(implies(p))),
            _ => None,
        },
        Expr::Eventually(inner) => match inner.as_ref() {
            Expr::Always(p) if is_state_level(p) => Some(eventually(always(implies(p)))),
            p if is_state_level(p) => Some(eventually(implies(p))),
            _ => None,
        },
        Expr::LeadsTo(p, q) => Some(Expr::LeadsTo(Box::new(and_guard(p)), q.clone())),
        Expr::BoxAction(action, subscript) => Some(Expr::BoxAction(
            Box::new(implies(action)),
            subscript.clone(),
        )),
        Expr::Forall(var, domain, inner) if !crate::eval::expr_references(guard, var) => {
            Some(Expr::Forall(
                var.clone(),
                domain.clone(),
                Box::new(push_guard(guard, inner)?),
            ))
        }
        _ => None,
    }
}

fn classify_into(
    expr: &Expr,
    mode: Classification,
    parts: &mut Vec<PropertyPart>,
) -> Result<(), String> {
    if is_state_level(expr) {
        parts.push(PropertyPart::Init(expr.clone()));
        return Ok(());
    }
    match expr {
        Expr::And(l, r) => {
            classify_into(l, mode, parts)?;
            classify_into(r, mode, parts)
        }
        Expr::Or(_, _) if mode == Classification::Syntactic => {
            parts.push(PropertyPart::Liveness(expr.clone()));
            Ok(())
        }
        Expr::Or(l, r) => {
            let mut disjuncts = Vec::new();
            classify_into(l, mode, &mut disjuncts)?;
            classify_into(r, mode, &mut disjuncts)?;
            if !disjuncts
                .iter()
                .all(|part| matches!(part, PropertyPart::Liveness(_)))
            {
                return Err(
                    "a disjunction with a disjunct that is not a liveness property (such as \
                     `x = 1 \\/ <>P` or `[]P \\/ []Q`) is not supported in a PROPERTY yet"
                        .to_string(),
                );
            }
            parts.extend(disjuncts);
            Ok(())
        }
        Expr::Always(inner) if is_state_level(inner) => {
            parts.push(PropertyPart::Invariant((**inner).clone()));
            Ok(())
        }
        Expr::BoxAction(_, _) => {
            parts.push(PropertyPart::Action(expr.clone()));
            Ok(())
        }
        Expr::Forall(var, domain, body) => {
            let bind = |inner: Expr| Expr::Forall(var.clone(), domain.clone(), Box::new(inner));
            let mut has_liveness = false;
            let mut body_parts = Vec::new();
            classify_into(body, mode, &mut body_parts)?;
            for part in body_parts {
                match part {
                    PropertyPart::Init(p) => parts.push(PropertyPart::Init(bind(p))),
                    PropertyPart::Invariant(p) => parts.push(PropertyPart::Invariant(bind(p))),
                    PropertyPart::Action(f) => parts.push(PropertyPart::Action(bind(f))),
                    PropertyPart::Liveness(_) => has_liveness = true,
                }
            }
            if has_liveness {
                parts.push(PropertyPart::Liveness(expr.clone()));
            }
            Ok(())
        }
        _ if mode == Classification::Syntactic => {
            parts.push(PropertyPart::Liveness(expr.clone()));
            Ok(())
        }
        _ => {
            parts.push(PropertyPart::Liveness(liveness_form(expr)?));
            Ok(())
        }
    }
}

fn liveness_form(expr: &Expr) -> Result<Expr, String> {
    let unsupported = |what: &str| Err(format!("{what} is not supported in a PROPERTY yet"));
    match expr {
        Expr::LeadsTo(p, q) if is_state_level(p) && is_state_level(q) => Ok(expr.clone()),
        Expr::Eventually(inner) => match inner.as_ref() {
            Expr::Always(p) if is_state_level(p) => Ok(expr.clone()),
            other if is_state_level(other) => Ok(expr.clone()),
            _ => unsupported("`<>` applied to a temporal formula"),
        },
        Expr::Always(inner) => {
            if let Some((p, q)) = leads_to_form(expr) {
                return Ok(Expr::LeadsTo(Box::new(p.clone()), Box::new(q.clone())));
            }
            match inner.as_ref() {
                Expr::Eventually(p) if is_state_level(p) => Ok((**p).clone()),
                _ => unsupported("a `[]` formula other than `[]P`, `[]<>P` or `[](P => <>Q)`"),
            }
        }
        Expr::Exists(var, domain, body) => match distribute_exists(var, domain, body) {
            Some(property) => Ok(property),
            None => unsupported("`\\E x \\in S : P` with a body other than `<>Q` or `[]<>Q`"),
        },
        Expr::WeakFairness(_, _) | Expr::StrongFairness(_, _) => {
            unsupported("a fairness formula (`WF`/`SF`)")
        }
        Expr::BoxAction(_, _) | Expr::DiamondAction(_, _) => {
            unsupported("an action-level formula other than a `[][A]_v` conjunct")
        }
        Expr::Implies(_, _) | Expr::If(_, _, _) => unsupported(
            "a temporal formula guarded by a condition on the state (`P => []Q`, `IF P THEN ..`)",
        ),
        _ => unsupported("this temporal formula"),
    }
}

#[derive(Debug, Clone)]
pub struct GuardEval {
    pub expression: String,
    pub result: bool,
    pub bindings: Vec<(String, Value)>,
}

#[derive(Debug, Clone)]
pub struct TransitionWithGuards {
    pub transition: Transition,
    pub guards: Vec<GuardEval>,
    pub parameter_bindings: Vec<(String, Value)>,
}

#[derive(Debug, Clone)]
pub struct VarChange {
    pub state_idx: usize,
    pub path: String,
    pub old_value: Value,
    pub new_value: Value,
    pub action: Option<Arc<str>>,
}

#[derive(Debug, Clone)]
pub struct SubExprEval {
    pub expression: String,
    pub value: Value,
    pub passed: bool,
}

#[derive(Debug, Clone)]
pub struct InvariantViolationInfo {
    pub name: String,
    pub failing_bindings: Vec<(String, Value)>,
    pub subexpression_evals: Vec<SubExprEval>,
}
