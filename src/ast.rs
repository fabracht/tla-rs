use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Str(Arc<str>),
    Set(BTreeSet<Value>),
    Fn(BTreeMap<Value, Value>),
    Record(BTreeMap<Arc<str>, Value>),
    Tuple(Vec<Value>),
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
    WeakFairness(Arc<str>, Box<Expr>),
    StrongFairness(Arc<str>, Box<Expr>),
    BoxAction(Box<Expr>, Arc<str>),
    DiamondAction(Box<Expr>, Arc<str>),
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

pub struct Spec {
    pub vars: Vec<Arc<str>>,
    pub constants: Vec<Arc<str>>,
    pub extends: Vec<Arc<str>>,
    pub definitions: BTreeMap<Arc<str>, (Vec<Arc<str>>, Expr)>,
    pub assumes: Vec<Expr>,
    pub instances: Vec<InstanceDecl>,
    pub init: Option<Expr>,
    pub next: Option<Expr>,
    pub invariants: Vec<Expr>,
    pub invariant_names: Vec<Option<Arc<str>>>,
    pub fairness: Vec<FairnessConstraint>,
    pub liveness_properties: Vec<Expr>,
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
