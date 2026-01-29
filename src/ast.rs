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

    QualifiedCall(Arc<str>, Arc<str>, Vec<Expr>),

    LabeledAction(Arc<str>, Box<Expr>),
}

pub type Env = BTreeMap<Arc<str>, Value>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    pub values: Vec<Value>,
}

#[derive(Debug, Clone)]
pub struct InstanceDecl {
    pub alias: Option<Arc<str>>,
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
    pub init: Expr,
    pub next: Expr,
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
