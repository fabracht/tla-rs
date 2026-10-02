//! Temporal formulas in negation normal form, the input of the tableau.
//!
//! A formula is built from atoms (state predicates, and `[A]_v` steps evaluated on a
//! transition), `/\`, `\/`, `[]` and `<>`, with negation only on atoms. Everything
//! else a TLA+ property can say is rewritten into that shape while it is built:
//! `~>`, `=>`, `<=>` and `IF` over temporal formulas, `<<A>>_v` as the negation of
//! `[~A]_v`, and `\A x \in S` / `\E x \in S` as the conjunction / disjunction of the
//! instances over a constant `S`.

use crate::ast::{Expr, Value, has_temporal_operator};
use crate::eval::{Definitions, contains_prime_ref_resolving_lets};

/// What an atom constrains: a state predicate holds at a position of a behavior, a
/// step `[A]_v` holds on the transition from that position to the next.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    State(Expr),
    Step { action: Expr, subscript: Expr },
}

#[derive(Debug, Clone, Default)]
pub struct AtomTable {
    atoms: Vec<Atom>,
}

impl AtomTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn atoms(&self) -> &[Atom] {
        &self.atoms
    }

    #[cfg(test)]
    pub(crate) fn intern_for_test(&mut self, atom: Atom) -> usize {
        self.intern(atom)
    }

    fn intern(&mut self, atom: Atom) -> usize {
        match self.atoms.iter().position(|known| *known == atom) {
            Some(index) => index,
            None => {
                self.atoms.push(atom);
                self.atoms.len() - 1
            }
        }
    }
}

/// A literal: atom `atom` holds (`positive`) or does not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    pub atom: usize,
    pub positive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ltl {
    True,
    False,
    Literal(Literal),
    And(Vec<Ltl>),
    Or(Vec<Ltl>),
    Always(Box<Ltl>),
    Eventually(Box<Ltl>),
}

/// Evaluates the set a quantifier ranges over; it must not depend on the state.
pub type DomainEval<'a> = dyn FnMut(&Expr) -> Result<Vec<Value>, String> + 'a;

pub struct Builder<'a, 'b> {
    pub atoms: &'a mut AtomTable,
    pub defs: &'a Definitions,
    pub domain: &'a mut DomainEval<'b>,
}

impl Builder<'_, '_> {
    /// `expr` (or its negation when `positive` is false) in negation normal form.
    pub fn build(&mut self, expr: &Expr, positive: bool) -> Result<Ltl, String> {
        if !has_temporal_operator(expr) {
            return self.state(expr, positive);
        }
        let dual = |positive: bool, conj: Vec<Ltl>| {
            if positive {
                Ltl::And(conj)
            } else {
                Ltl::Or(conj)
            }
        };
        match expr {
            Expr::Not(inner) => self.build(inner, !positive),
            Expr::And(l, r) => Ok(dual(
                positive,
                vec![self.build(l, positive)?, self.build(r, positive)?],
            )),
            Expr::Or(l, r) => Ok(dual(
                !positive,
                vec![self.build(l, positive)?, self.build(r, positive)?],
            )),
            Expr::Implies(l, r) => Ok(dual(
                !positive,
                vec![self.build(l, !positive)?, self.build(r, positive)?],
            )),
            Expr::Equiv(l, r) => {
                let (l_true, l_false) = (self.build(l, true)?, self.build(l, false)?);
                let (r_true, r_false) = (self.build(r, true)?, self.build(r, false)?);
                let (same, differ) = (
                    Ltl::Or(vec![
                        Ltl::And(vec![l_true.clone(), r_true.clone()]),
                        Ltl::And(vec![l_false.clone(), r_false.clone()]),
                    ]),
                    Ltl::Or(vec![
                        Ltl::And(vec![l_true, r_false]),
                        Ltl::And(vec![l_false, r_true]),
                    ]),
                );
                Ok(if positive { same } else { differ })
            }
            Expr::If(cond, then_branch, else_branch) => {
                if has_temporal_operator(cond) {
                    return Err("an IF condition must not be a temporal formula".to_string());
                }
                let branch = |this: &mut Self, taken: bool, branch: &Expr| -> Result<Ltl, String> {
                    Ok(Ltl::And(vec![
                        this.state(cond, taken)?,
                        this.build(branch, positive)?,
                    ]))
                };
                Ok(Ltl::Or(vec![
                    branch(self, true, then_branch)?,
                    branch(self, false, else_branch)?,
                ]))
            }
            Expr::Always(inner) => {
                let inner = self.build(inner, positive)?;
                Ok(if positive {
                    Ltl::Always(Box::new(inner))
                } else {
                    Ltl::Eventually(Box::new(inner))
                })
            }
            Expr::Eventually(inner) => {
                let inner = self.build(inner, positive)?;
                Ok(if positive {
                    Ltl::Eventually(Box::new(inner))
                } else {
                    Ltl::Always(Box::new(inner))
                })
            }
            Expr::LeadsTo(p, q) => {
                let expanded = Expr::Always(Box::new(Expr::Implies(
                    p.clone(),
                    Box::new(Expr::Eventually(q.clone())),
                )));
                self.build(&expanded, positive)
            }
            Expr::BoxAction(action, subscript) => {
                let step = self.step(action, subscript, positive)?;
                Ok(if positive {
                    Ltl::Always(Box::new(step))
                } else {
                    Ltl::Eventually(Box::new(step))
                })
            }
            Expr::DiamondAction(action, subscript) => {
                let negated = Expr::Not(action.clone());
                self.step(&negated, subscript, !positive)
            }
            Expr::Forall(var, domain, body) | Expr::Exists(var, domain, body) => {
                let universal = matches!(expr, Expr::Forall(..));
                let mut instances = Vec::new();
                for element in (self.domain)(domain)? {
                    let subs = [(var.clone(), Expr::Lit(element))];
                    let concrete = crate::substitution::substitute_expr(body, &subs);
                    instances.push(self.build(&concrete, positive)?);
                }
                Ok(dual(universal == positive, instances))
            }
            Expr::WeakFairness(_, _) | Expr::StrongFairness(_, _) => Err(
                "a fairness formula (`WF`/`SF`) is not supported inside a temporal formula yet"
                    .to_string(),
            ),
            _ => Err(format!("unsupported temporal formula: {expr:?}")),
        }
    }

    fn state(&mut self, expr: &Expr, positive: bool) -> Result<Ltl, String> {
        if let Expr::Lit(Value::Bool(value)) = expr {
            return Ok(if *value == positive {
                Ltl::True
            } else {
                Ltl::False
            });
        }
        self.reject_run_dependent(expr)?;
        if crate::eval::uses_enabled(expr, self.defs) {
            return Err("ENABLED is not supported in a temporal formula yet".to_string());
        }
        if contains_prime_ref_resolving_lets(expr, self.defs) {
            return Err(
                "an action formula must appear as `[][A]_v` or `<<A>>_v` in a temporal formula"
                    .to_string(),
            );
        }
        let atom = self.atoms.intern(Atom::State(expr.clone()));
        Ok(Ltl::Literal(Literal { atom, positive }))
    }

    fn reject_run_dependent(&self, expr: &Expr) -> Result<(), String> {
        if crate::eval::uses_run_dependent_builtin(expr, self.defs) {
            return Err(
                "TLCGet, RandomElement and the time built-ins are not supported in a temporal \
                 formula: their value depends on the run, not on the state"
                    .to_string(),
            );
        }
        Ok(())
    }

    fn step(&mut self, action: &Expr, subscript: &Expr, positive: bool) -> Result<Ltl, String> {
        self.reject_run_dependent(action)?;
        self.reject_run_dependent(subscript)?;
        let atom = self.atoms.intern(Atom::Step {
            action: action.clone(),
            subscript: subscript.clone(),
        });
        Ok(Ltl::Literal(Literal { atom, positive }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Env;
    use crate::eval::eval;
    use crate::parser::parse_expr;

    fn build(source: &str, positive: bool) -> Result<(Ltl, AtomTable), String> {
        let expr = parse_expr(source).map_err(|e| e.message)?;
        let defs = Definitions::new();
        let mut atoms = AtomTable::new();
        let mut domain = |set: &Expr| match eval(set, &mut Env::new(), &defs) {
            Ok(Value::Set(elements)) => Ok(elements.iter().cloned().collect()),
            other => Err(format!("not a set: {other:?}")),
        };
        let formula = Builder {
            atoms: &mut atoms,
            defs: &defs,
            domain: &mut domain,
        }
        .build(&expr, positive)?;
        Ok((formula, atoms))
    }

    fn literal(atom: usize, positive: bool) -> Ltl {
        Ltl::Literal(Literal { atom, positive })
    }

    fn state_atom(atoms: &AtomTable, index: usize) -> String {
        match &atoms.atoms()[index] {
            Atom::State(expr) => format!("{expr:?}"),
            Atom::Step { .. } => panic!("atom {index} is a step"),
        }
    }

    #[test]
    fn negation_is_pushed_to_the_atoms() {
        let (formula, atoms) = build("~<>(x = 1)", true).unwrap();
        assert_eq!(formula, Ltl::Always(Box::new(literal(0, false))));
        assert!(state_atom(&atoms, 0).contains("Eq"));
        let (negated, _) = build("[]<>(x = 1)", false).unwrap();
        assert_eq!(
            negated,
            Ltl::Eventually(Box::new(Ltl::Always(Box::new(literal(0, false)))))
        );
    }

    #[test]
    fn leads_to_expands_to_always_implies_eventually() {
        let (formula, _) = build("(x = 0) ~> (x = 1)", true).unwrap();
        assert_eq!(
            formula,
            Ltl::Always(Box::new(Ltl::Or(vec![
                literal(0, false),
                Ltl::Eventually(Box::new(literal(1, true))),
            ])))
        );
    }

    #[test]
    fn quantifiers_expand_over_their_domain() {
        let (forall, atoms) = build("\\A i \\in {1, 2} : <>(x = i)", true).unwrap();
        assert_eq!(
            forall,
            Ltl::And(vec![
                Ltl::Eventually(Box::new(literal(0, true))),
                Ltl::Eventually(Box::new(literal(1, true))),
            ])
        );
        assert_eq!(atoms.atoms().len(), 2, "one atom per instance");
        let (exists, _) = build("\\E i \\in {1, 2} : <>(x = i)", false).unwrap();
        assert!(
            matches!(exists, Ltl::And(ref parts) if parts.len() == 2),
            "~\\E is the conjunction of the negated instances: {exists:?}"
        );
    }

    #[test]
    fn box_and_diamond_actions_become_step_literals() {
        let (boxed, atoms) = build("[][x' > x]_x", true).unwrap();
        assert_eq!(boxed, Ltl::Always(Box::new(literal(0, true))));
        assert!(matches!(atoms.atoms()[0], Atom::Step { .. }));
        let (negated, _) = build("[][x' > x]_x", false).unwrap();
        assert_eq!(negated, Ltl::Eventually(Box::new(literal(0, false))));
        let (diamond, atoms) = build("[]<><<x' > x>>_x", true).unwrap();
        assert_eq!(
            diamond,
            Ltl::Always(Box::new(Ltl::Eventually(Box::new(literal(0, false))))),
            "<<A>>_v is the negation of [~A]_v"
        );
        assert!(matches!(
            &atoms.atoms()[0],
            Atom::Step {
                action: Expr::Not(_),
                ..
            }
        ));
    }

    #[test]
    fn if_over_temporal_branches_splits_on_its_condition() {
        let (formula, _) = build("IF y = 0 THEN [](x = 1) ELSE <>(x = 2)", true).unwrap();
        assert_eq!(
            formula,
            Ltl::Or(vec![
                Ltl::And(vec![
                    literal(0, true),
                    Ltl::Always(Box::new(literal(1, true)))
                ]),
                Ltl::And(vec![
                    literal(0, false),
                    Ltl::Eventually(Box::new(literal(2, true)))
                ]),
            ])
        );
    }

    #[test]
    fn constants_fold_and_bare_actions_are_rejected() {
        let (formula, atoms) = build("[](TRUE) /\\ <>(FALSE)", true).unwrap();
        assert_eq!(
            formula,
            Ltl::And(vec![
                Ltl::Always(Box::new(Ltl::True)),
                Ltl::Eventually(Box::new(Ltl::False)),
            ])
        );
        assert!(atoms.atoms().is_empty());
        let error = build("<>(x' = x + 1)", true).unwrap_err();
        assert!(error.contains("[][A]_v"), "{error}");
    }
}
