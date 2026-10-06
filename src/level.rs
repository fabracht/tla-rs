use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::ast::{DefinitionMap, Expr};

/// The level of a TLA+ expression: whether its value depends on nothing, on a state,
/// on a step, or on a whole behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    Constant,
    State,
    Action,
    Temporal,
}

/// Two measures of an expression's level. `exact` is SANY's: a `LET` has the level
/// of its body, and an operator application that of the operator's body with each
/// parameter at its argument's level, so an action used only under `ENABLED` leaves
/// no trace. `bound` is the coarser bound TLC classifies a `PROPERTY` by: a `LET`
/// also counts its definitions, and an application its arguments, used or not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Levels {
    pub exact: Level,
    pub bound: Level,
}

impl Levels {
    const CONSTANT: Levels = Levels::both(Level::Constant);

    const fn both(level: Level) -> Self {
        Levels {
            exact: level,
            bound: level,
        }
    }

    fn max(self, other: Levels) -> Levels {
        Levels {
            exact: self.exact.max(other.exact),
            bound: self.bound.max(other.bound),
        }
    }
}

#[derive(Clone)]
enum Local {
    Value(Levels),
    Operator(Vec<Arc<str>>, Expr),
}

/// Computes [`Levels`] over a module's variables and definitions. Each definition
/// is analysed once per combination of argument levels, so the work is linear in the
/// size of the definitions however often they are called. Only what the module
/// itself defines is consulted: an operator of an `INSTANCE` (`I!Op`) is taken at
/// the level of its arguments.
pub struct LevelAnalysis<'a> {
    vars: &'a [Arc<str>],
    defs: &'a DefinitionMap,
    applications: HashMap<(Arc<str>, Vec<Levels>), Levels>,
    in_progress: HashSet<Arc<str>>,
}

impl<'a> LevelAnalysis<'a> {
    pub fn new(vars: &'a [Arc<str>], defs: &'a DefinitionMap) -> Self {
        LevelAnalysis {
            vars,
            defs,
            applications: HashMap::new(),
            in_progress: HashSet::new(),
        }
    }

    pub fn levels(&mut self, expr: &Expr) -> Levels {
        self.levels_in(expr, &mut Vec::new())
    }

    fn levels_in(&mut self, expr: &Expr, locals: &mut Vec<(Arc<str>, Local)>) -> Levels {
        match expr {
            Expr::Prime(_) | Expr::Unchanged(_) => Levels::both(Level::Action),
            Expr::EnabledOp(_) => Levels::both(Level::State),
            Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFairness(_, _)
            | Expr::StrongFairness(_, _)
            | Expr::BoxAction(_, _)
            | Expr::DiamondAction(_, _) => Levels::both(Level::Temporal),
            Expr::Var(name) => self.name_levels(name, locals),
            Expr::Lit(_)
            | Expr::OldValue
            | Expr::Any
            | Expr::EmptyBag
            | Expr::JavaTime
            | Expr::SystemTime => Levels::CONSTANT,
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
            | Expr::RecordAccess(e, _)
            | Expr::TupleAccess(e, _)
            | Expr::LabeledAction(_, e) => self.levels_in(e, locals),
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
            | Expr::SqSubseteq(l, r) => self.levels_in(l, locals).max(self.levels_in(r, locals)),
            Expr::If(a, b, c) | Expr::SubSeq(a, b, c) => self
                .levels_in(a, locals)
                .max(self.levels_in(b, locals))
                .max(self.levels_in(c, locals)),
            Expr::Forall(var, domain, body)
            | Expr::Exists(var, domain, body)
            | Expr::Choose(var, domain, body)
            | Expr::FnDef(var, domain, body)
            | Expr::SetFilter(var, domain, body)
            | Expr::SetMap(var, domain, body) => {
                let domain = self.levels_in(domain, locals);
                domain.max(self.bound_levels(std::slice::from_ref(var), body, locals))
            }
            Expr::ChooseUnbounded(var, body) => {
                self.bound_levels(std::slice::from_ref(var), body, locals)
            }
            Expr::Lambda(params, body) => self.bound_levels(params, body, locals),
            Expr::SetEnum(items) | Expr::TupleLit(items) => self.all_levels(items, locals),
            Expr::RecordLit(fields) | Expr::RecordSet(fields) => {
                fields.iter().fold(Levels::CONSTANT, |acc, (_, e)| {
                    acc.max(self.levels_in(e, locals))
                })
            }
            Expr::Except(base, updates) => {
                updates
                    .iter()
                    .fold(self.levels_in(base, locals), |acc, (path, value)| {
                        acc.max(self.all_levels(path, locals))
                            .max(self.levels_in(value, locals))
                    })
            }
            Expr::Case(branches) => branches.iter().fold(Levels::CONSTANT, |acc, (c, r)| {
                acc.max(self.levels_in(c, locals))
                    .max(self.levels_in(r, locals))
            }),
            Expr::FnCall(name, args) => self.application(name, args, locals),
            Expr::CustomOp(name, l, r) => {
                self.application(name, &[(**l).clone(), (**r).clone()], locals)
            }
            Expr::QualifiedCall(_, _, args) => self.all_levels(args, locals),
            Expr::Let(name, binding, body) => self.let_levels(name, binding, body, locals),
        }
    }

    fn all_levels(&mut self, items: &[Expr], locals: &mut Vec<(Arc<str>, Local)>) -> Levels {
        items.iter().fold(Levels::CONSTANT, |acc, e| {
            acc.max(self.levels_in(e, locals))
        })
    }

    fn bound_levels(
        &mut self,
        names: &[Arc<str>],
        body: &Expr,
        locals: &mut Vec<(Arc<str>, Local)>,
    ) -> Levels {
        let depth = locals.len();
        locals.extend(
            names
                .iter()
                .map(|name| (name.clone(), Local::Value(Levels::CONSTANT))),
        );
        let levels = self.levels_in(body, locals);
        locals.truncate(depth);
        levels
    }

    fn name_levels(&mut self, name: &Arc<str>, locals: &mut Vec<(Arc<str>, Local)>) -> Levels {
        if let Some((_, local)) = locals.iter().rev().find(|(bound, _)| bound == name) {
            return match local.clone() {
                Local::Value(levels) => levels,
                Local::Operator(params, body) => self.bound_levels(&params, &body, locals),
            };
        }
        if self.vars.contains(name) {
            return Levels::both(Level::State);
        }
        if self.defs.contains_key(name) {
            return self.application(name, &[], &mut Vec::new());
        }
        Levels::CONSTANT
    }

    fn let_levels(
        &mut self,
        name: &Arc<str>,
        binding: &Expr,
        body: &Expr,
        locals: &mut Vec<(Arc<str>, Local)>,
    ) -> Levels {
        let (local, definition) = match crate::eval::parameterized_let_op(binding) {
            Some((params, op_body)) => {
                let definition = self.bound_levels(&params, op_body, locals);
                (Local::Operator(params, op_body.clone()), definition)
            }
            None => {
                let definition = self.levels_in(binding, locals);
                (Local::Value(definition), definition)
            }
        };
        locals.push((name.clone(), local));
        let inner = self.levels_in(body, locals);
        locals.pop();
        Levels {
            exact: inner.exact,
            bound: inner.bound.max(definition.bound),
        }
    }

    fn application(
        &mut self,
        name: &Arc<str>,
        args: &[Expr],
        locals: &mut Vec<(Arc<str>, Local)>,
    ) -> Levels {
        let arg_levels: Vec<Levels> = args.iter().map(|arg| self.levels_in(arg, locals)).collect();
        let arguments = arg_levels
            .iter()
            .fold(Levels::CONSTANT, |acc, l| acc.max(*l));
        let local = locals
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, local)| local.clone());
        let body = match local {
            Some(Local::Operator(params, body)) if params.len() == args.len() => {
                self.applied_body(&params, &body, &arg_levels, locals)
            }
            Some(_) => return arguments,
            None => match self.global_application(name, &arg_levels) {
                Some(body) => body,
                None => return arguments,
            },
        };
        Levels {
            exact: body.exact,
            bound: body.bound.max(arguments.bound),
        }
    }

    fn global_application(&mut self, name: &Arc<str>, arg_levels: &[Levels]) -> Option<Levels> {
        let (params, body) = self.defs.get(name)?;
        if params.len() != arg_levels.len() {
            return None;
        }
        let key = (name.clone(), arg_levels.to_vec());
        if let Some(levels) = self.applications.get(&key) {
            return Some(*levels);
        }
        if !self.in_progress.insert(name.clone()) {
            return Some(Levels::CONSTANT);
        }
        let (params, body) = (params.clone(), body.clone());
        let levels = self.applied_body(&params, &body, arg_levels, &mut Vec::new());
        self.in_progress.remove(name);
        self.applications.insert(key, levels);
        Some(levels)
    }

    fn applied_body(
        &mut self,
        params: &[Arc<str>],
        body: &Expr,
        arg_levels: &[Levels],
        locals: &mut Vec<(Arc<str>, Local)>,
    ) -> Levels {
        let depth = locals.len();
        locals.extend(
            params
                .iter()
                .cloned()
                .zip(arg_levels.iter().map(|l| Local::Value(*l))),
        );
        let levels = self.levels_in(body, locals);
        locals.truncate(depth);
        levels
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Classification, PropertyPart, classify_property};

    const MODULE: &str = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y\n\
        Inc == x < 2 /\\ x' = x + 1 /\\ y' = y\nChanged(v) == v' # v\nEn(a) == ENABLED a\n\
        P == TRUE\n====";

    fn classify(property: &str) -> Result<Vec<PropertyPart>, String> {
        let module = MODULE.replace("P == TRUE", &format!("P == {property}"));
        let spec = crate::parser::parse(&module).unwrap();
        let (_, body) = spec.definitions.get("P").unwrap();
        classify_property(
            body,
            &spec.vars,
            &spec.definitions,
            Classification::Syntactic,
        )
    }

    fn kind(property: &str) -> &'static str {
        match classify(property).unwrap().as_slice() {
            [PropertyPart::Invariant(_)] => "invariant",
            [PropertyPart::Liveness(_)] => "liveness",
            other => panic!("{property}: unexpected parts {other:?}"),
        }
    }

    #[test]
    fn always_over_an_action_is_rejected_as_in_sany() {
        for property in [
            "[](x' >= x)",
            "[]Changed(x)",
            "[](UNCHANGED y)",
            "[]({x' : z \\in {1}} = {x})",
        ] {
            let error = classify(property).unwrap_err();
            assert!(
                error.contains("not of the form [A]_v"),
                "{property}: {error}"
            );
        }
    }

    #[test]
    fn always_is_an_invariant_only_at_the_level_bound_of_a_state() {
        assert_eq!(kind("[](LET a == Inc IN ENABLED a)"), "liveness");
        assert_eq!(kind("[]En(Inc)"), "liveness");
        assert_eq!(kind("[](LET G(A) == ENABLED A IN G(Inc))"), "liveness");
        assert_eq!(kind("[](LET F(v) == v' = v IN x < 2)"), "liveness");
        assert_eq!(kind("[](ENABLED Inc)"), "invariant");
        assert_eq!(kind("[](ENABLED (LET a == Inc IN a))"), "invariant");
        assert_eq!(kind("[](LET a == ENABLED Inc IN a)"), "invariant");
        assert_eq!(kind("[](LET a == x + 1 IN a < 3)"), "invariant");
    }

    #[test]
    fn an_instance_operator_is_taken_at_the_level_of_its_arguments() {
        let spec = crate::parser::parse(
            "---- MODULE U ----\nVARIABLES x\nI == INSTANCE M\nP == []I!CanInc\n====",
        )
        .unwrap();
        let (_, body) = spec.definitions.get("P").unwrap();
        let parts = classify_property(
            body,
            &spec.vars,
            &spec.definitions,
            Classification::Syntactic,
        )
        .unwrap();
        assert!(matches!(parts.as_slice(), [PropertyPart::Invariant(_)]));
    }
}
