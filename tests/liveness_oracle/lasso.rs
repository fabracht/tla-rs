//! Independent validator for counterexamples reported by the checker.
//!
//! A counterexample is an ultimately periodic behavior `s0 .. s(k-1) (sk .. s(n-1))^ω`,
//! stored as `states` plus the index `loop_start` where the repeating part begins.
//! Temporal formulas are evaluated directly over lasso positions, so a verdict here
//! never depends on the checker's SCC analysis: state predicates and actions go
//! through the regular expression evaluator, and `ENABLED` / fairness enabledness
//! are computed from successors of the action itself.

use std::ops::Range;
use std::sync::Arc;

use tla_checker::ast::{Env, Expr, State, Value};
use tla_checker::eval::{Definitions, eval, make_primed_names, next_states};
use tla_checker::intern::primed_name;

pub type Verdict<T> = Result<T, String>;

pub struct Lasso {
    states: Vec<State>,
    loop_start: usize,
}

impl Lasso {
    pub fn new(states: Vec<State>, loop_start: usize) -> Verdict<Self> {
        if loop_start >= states.len() {
            return Err(format!(
                "loop start {loop_start} is outside a lasso of {} states",
                states.len()
            ));
        }
        Ok(Self { states, loop_start })
    }

    /// `prefix ++ cycle`, looping back to the first cycle state.
    pub fn from_prefix_and_cycle(prefix: &[State], cycle: &[State]) -> Verdict<Self> {
        let states: Vec<State> = prefix.iter().chain(cycle).cloned().collect();
        Self::new(states, prefix.len())
    }

    /// A finite trace extended by stuttering forever in its last state.
    pub fn stuttering_after(trace: &[State]) -> Verdict<Self> {
        Self::new(trace.to_vec(), trace.len().saturating_sub(1))
    }

    fn succ(&self, pos: usize) -> usize {
        if pos + 1 < self.states.len() {
            pos + 1
        } else {
            self.loop_start
        }
    }

    fn suffix(&self, pos: usize) -> Range<usize> {
        pos.min(self.loop_start)..self.states.len()
    }

    fn cycle(&self) -> Range<usize> {
        self.loop_start..self.states.len()
    }
}

pub struct Model<'a> {
    pub vars: &'a [Arc<str>],
    pub constants: &'a Env,
    pub defs: &'a Definitions,
}

impl Model<'_> {
    fn state_env(&self, state: &State, bound: &Env) -> Env {
        let mut env = self.constants.clone();
        for (name, value) in bound {
            env.insert(name.clone(), value.clone());
        }
        for (var, value) in self.vars.iter().zip(&state.values) {
            env.insert(var.clone(), value.clone());
        }
        env
    }

    fn step_env(&self, current: &State, next: &State, bound: &Env) -> Env {
        let mut env = self.state_env(current, bound);
        for (var, value) in self.vars.iter().zip(&next.values) {
            env.insert(primed_name(var), value.clone());
        }
        env
    }

    fn eval_bool(&self, expr: &Expr, env: &mut Env) -> Verdict<bool> {
        match eval(expr, env, self.defs) {
            Ok(Value::Bool(b)) => Ok(b),
            Ok(other) => Err(format!("expected a boolean, got {other:?} from {expr:?}")),
            Err(e) => Err(format!("eval error {e:?} in {expr:?}")),
        }
    }

    fn successors(&self, action: &Expr, state: &State, bound: &Env) -> Verdict<Vec<State>> {
        let mut env = self.constants.clone();
        for (name, value) in bound {
            env.insert(name.clone(), value.clone());
        }
        let primed = make_primed_names(self.vars);
        next_states(action, state, self.vars, &primed, &mut env, self.defs)
            .map(|transitions| transitions.into_iter().map(|t| t.state).collect())
            .map_err(|e| format!("successor enumeration failed for {action:?}: {e:?}"))
    }

    fn subscript_changes(
        &self,
        subscript: &str,
        current: &State,
        next: &State,
        bound: &Env,
    ) -> Verdict<bool> {
        let expr = Expr::Var(Arc::from(subscript));
        let before = eval(&expr, &mut self.state_env(current, bound), self.defs)
            .map_err(|e| format!("subscript {subscript} failed to evaluate: {e:?}"))?;
        let after = eval(&expr, &mut self.state_env(next, bound), self.defs)
            .map_err(|e| format!("subscript {subscript} failed to evaluate: {e:?}"))?;
        Ok(before != after)
    }

    /// `<<A>>_v` on the step `current -> next`.
    fn angle_step(
        &self,
        action: &Expr,
        subscript: &str,
        current: &State,
        next: &State,
        bound: &Env,
    ) -> Verdict<bool> {
        Ok(self.subscript_changes(subscript, current, next, bound)?
            && self.eval_bool(action, &mut self.step_env(current, next, bound))?)
    }

    /// `ENABLED <<A>>_v` in `state`.
    fn angle_enabled(
        &self,
        action: &Expr,
        subscript: &str,
        state: &State,
        bound: &Env,
    ) -> Verdict<bool> {
        for next in self.successors(action, state, bound)? {
            if self.subscript_changes(subscript, state, &next, bound)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `WF_v(A)` / `SF_v(A)` on the lasso. Both are suffix-closed, so only the
    /// cycle decides them: weak fairness fails when `<<A>>_v` is enabled in every
    /// cycle state yet never taken on a cycle step; strong fairness fails when it
    /// is enabled in some cycle state yet never taken.
    fn fairness_holds(
        &self,
        lasso: &Lasso,
        strong: bool,
        subscript: &str,
        action: &Expr,
        bound: &Env,
    ) -> Verdict<bool> {
        let mut taken = false;
        for pos in lasso.cycle() {
            let next = &lasso.states[lasso.succ(pos)];
            if self.angle_step(action, subscript, &lasso.states[pos], next, bound)? {
                taken = true;
                break;
            }
        }
        if taken {
            return Ok(true);
        }
        let mut enabled = Vec::new();
        for pos in lasso.cycle() {
            enabled.push(self.angle_enabled(action, subscript, &lasso.states[pos], bound)?);
        }
        let demanded = if strong {
            enabled.iter().any(|e| *e)
        } else {
            enabled.iter().all(|e| *e)
        };
        Ok(!demanded)
    }

    fn domain(&self, domain: &Expr, bound: &Env) -> Verdict<Vec<Value>> {
        let mut env = self.constants.clone();
        for (name, value) in bound {
            env.insert(name.clone(), value.clone());
        }
        match eval(domain, &mut env, self.defs) {
            Ok(Value::Set(elements)) => Ok(elements.iter().cloned().collect()),
            Ok(other) => Err(format!(
                "quantifier domain must be a finite constant set, got {other:?}"
            )),
            Err(e) => Err(format!("quantifier domain failed to evaluate: {e:?}")),
        }
    }

    fn temporal_definition(&self, name: &Arc<str>, bound: &Env) -> Option<&Expr> {
        if bound.contains_key(name) || self.vars.contains(name) {
            return None;
        }
        match self.defs.get(name) {
            Some((params, body)) if params.is_empty() => Some(body.as_ref()),
            _ => None,
        }
    }

    /// Truth of `formula` at lasso position `pos`, with quantifier bindings `bound`.
    pub fn holds(&self, lasso: &Lasso, formula: &Expr, pos: usize, bound: &Env) -> Verdict<bool> {
        match formula {
            Expr::Always(inner) => {
                for j in lasso.suffix(pos) {
                    if !self.holds(lasso, inner, j, bound)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Expr::Eventually(inner) => {
                for j in lasso.suffix(pos) {
                    if self.holds(lasso, inner, j, bound)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Expr::LeadsTo(p, q) => {
                for j in lasso.suffix(pos) {
                    if self.holds(lasso, p, j, bound)? {
                        let mut reached = false;
                        for k in lasso.suffix(j) {
                            if self.holds(lasso, q, k, bound)? {
                                reached = true;
                                break;
                            }
                        }
                        if !reached {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            Expr::Not(inner) => Ok(!self.holds(lasso, inner, pos, bound)?),
            Expr::And(l, r) => {
                Ok(self.holds(lasso, l, pos, bound)? && self.holds(lasso, r, pos, bound)?)
            }
            Expr::Or(l, r) => {
                Ok(self.holds(lasso, l, pos, bound)? || self.holds(lasso, r, pos, bound)?)
            }
            Expr::Implies(l, r) => {
                Ok(!self.holds(lasso, l, pos, bound)? || self.holds(lasso, r, pos, bound)?)
            }
            Expr::Equiv(l, r) => {
                Ok(self.holds(lasso, l, pos, bound)? == self.holds(lasso, r, pos, bound)?)
            }
            Expr::Forall(var, domain, body) => {
                for element in self.domain(domain, bound)? {
                    let mut inner = bound.clone();
                    inner.insert(var.clone(), element);
                    if !self.holds(lasso, body, pos, &inner)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Expr::Exists(var, domain, body) => {
                for element in self.domain(domain, bound)? {
                    let mut inner = bound.clone();
                    inner.insert(var.clone(), element);
                    if self.holds(lasso, body, pos, &inner)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Expr::BoxAction(action, subscript) => {
                for j in lasso.suffix(pos) {
                    let current = &lasso.states[j];
                    let next = &lasso.states[lasso.succ(j)];
                    if self.subscript_changes(subscript, current, next, bound)?
                        && !self.eval_bool(action, &mut self.step_env(current, next, bound))?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Expr::DiamondAction(action, subscript) => self.angle_step(
                action,
                subscript,
                &lasso.states[pos],
                &lasso.states[lasso.succ(pos)],
                bound,
            ),
            Expr::WeakFairness(subscript, action) => {
                self.fairness_holds(lasso, false, subscript, action, bound)
            }
            Expr::StrongFairness(subscript, action) => {
                self.fairness_holds(lasso, true, subscript, action, bound)
            }
            Expr::EnabledOp(action) => Ok(!self
                .successors(action, &lasso.states[pos], bound)?
                .is_empty()),
            Expr::Var(name) => match self.temporal_definition(name, bound) {
                Some(body) => self.holds(lasso, body, pos, bound),
                None => self.leaf(lasso, formula, pos, bound),
            },
            _ => self.leaf(lasso, formula, pos, bound),
        }
    }

    fn leaf(&self, lasso: &Lasso, formula: &Expr, pos: usize, bound: &Env) -> Verdict<bool> {
        let current = &lasso.states[pos];
        let next = &lasso.states[lasso.succ(pos)];
        self.eval_bool(formula, &mut self.step_env(current, next, bound))
    }

    /// Every lasso step (prefix, prefix-to-cycle, and the wraparound) must be a
    /// stutter or a successor of `next`, and the first state must satisfy `init`.
    pub fn check_is_behavior(&self, lasso: &Lasso, init: &Expr, next: &Expr) -> Verdict<()> {
        let empty = Env::new();
        let first = &lasso.states[0];
        if !self.eval_bool(init, &mut self.state_env(first, &empty))? {
            return Err(format!("first state {first:?} does not satisfy Init"));
        }
        for pos in 0..lasso.states.len() {
            let current = &lasso.states[pos];
            let target = &lasso.states[lasso.succ(pos)];
            if current == target {
                continue;
            }
            if !self.successors(next, current, &empty)?.contains(target) {
                return Err(format!(
                    "step {pos} -> {} ({current:?} -> {target:?}) is neither a stutter nor a Next successor",
                    lasso.succ(pos)
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_checker::checker::prepare_spec;
    use tla_checker::parser::parse;

    const WALK: &str = "---- MODULE W ----\n\
        EXTENDS Naturals\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Step == x < 2 /\\ x' = x + 1\n\
        Next == Step \\/ UNCHANGED x\n\
        ====\n";

    struct Fixture {
        vars: Vec<Arc<str>>,
        constants: Env,
        defs: Definitions,
    }

    impl Fixture {
        fn new() -> Self {
            let spec = parse(WALK).expect("fixture parses");
            let (constants, defs) =
                prepare_spec(&spec, &Env::new(), None, true).expect("fixture prepares");
            Self {
                vars: spec.vars.clone(),
                constants,
                defs,
            }
        }

        fn model(&self) -> Model<'_> {
            Model {
                vars: &self.vars,
                constants: &self.constants,
                defs: &self.defs,
            }
        }
    }

    fn formula(text: &str) -> Expr {
        let module = format!(
            "---- MODULE F ----\nEXTENDS Naturals\nVARIABLE x\nStep == x < 2 /\\ x' = x + 1\nF == {text}\n====\n"
        );
        let spec = parse(&module).expect("formula parses");
        spec.definitions
            .get("F")
            .map(|(_, body)| body.as_ref().clone())
            .expect("F is defined")
    }

    fn lasso(xs: &[i64], loop_start: usize) -> Lasso {
        let states = xs
            .iter()
            .map(|x| State {
                values: vec![Value::Int(*x)],
            })
            .collect();
        Lasso::new(states, loop_start).expect("valid lasso")
    }

    fn truth(text: &str, xs: &[i64], loop_start: usize) -> bool {
        let fixture = Fixture::new();
        fixture
            .model()
            .holds(&lasso(xs, loop_start), &formula(text), 0, &Env::new())
            .expect("formula evaluates")
    }

    #[test]
    fn eventually_and_always_over_terminal_stutter() {
        assert!(truth("<>(x = 1)", &[0, 1, 2], 2));
        assert!(!truth("[]<>(x = 1)", &[0, 1, 2], 2));
        assert!(truth("<>[](x = 2)", &[0, 1, 2], 2));
        assert!(truth("[](x < 5)", &[0, 1, 2], 2));
        assert!(!truth("[](x < 2)", &[0, 1, 2], 2));
        assert!(!truth("<>(x = 1)", &[0], 0));
    }

    #[test]
    fn state_predicate_is_judged_at_the_first_position() {
        assert!(truth("x = 0", &[0, 1, 2], 2));
        assert!(!truth("x = 1", &[0, 1, 2], 2));
    }

    #[test]
    fn leads_to_distinguishes_prefix_from_cycle() {
        assert!(truth("(x = 0) ~> (x = 2)", &[0, 1, 2], 2));
        assert!(!truth("(x = 0) ~> (x = 2)", &[0, 1], 1));
        assert!(!truth("[](x = 0 => <>(x = 2))", &[0, 1], 1));
        assert!(truth("(x = 5) ~> (x = 7)", &[0, 1], 1));
    }

    #[test]
    fn nested_and_disjunctive_formulas() {
        assert!(truth("<>(x = 1) \\/ <>(x = 5)", &[0, 1, 2], 2));
        assert!(truth("<>(x = 1 /\\ <>(x = 2))", &[0, 1, 2], 2));
        assert!(!truth("<>(x = 2 /\\ <>(x = 1))", &[0, 1, 2], 2));
        assert!(truth("[](x = 2 => [](x = 2))", &[0, 1, 2], 2));
        assert!(truth("<>[](x = 1) \\/ <>[](x = 2)", &[0, 1, 2], 2));
        assert!(!truth("<>[](x = 1) \\/ <>[](x = 2)", &[0, 1], 0));
    }

    #[test]
    fn quantifiers_over_constant_domains() {
        assert!(truth("\\A i \\in {1, 2} : <>(x = i)", &[0, 1, 2], 2));
        assert!(!truth("\\A i \\in {1, 2} : <>(x = i)", &[0, 1], 1));
        assert!(truth("\\E i \\in {1, 2} : <>(x = i)", &[0, 1], 1));
        assert!(!truth("\\E i \\in {1, 5} : []<>(x = i)", &[0, 1, 2], 2));
        assert!(truth("\\E i \\in {1, 5} : []<>(x = i)", &[0, 1], 0));
    }

    #[test]
    fn action_level_formulas() {
        assert!(truth("[]<><<x' # x>>_x", &[0, 1], 0));
        assert!(!truth("[]<><<x' # x>>_x", &[0, 1, 2], 2));
        assert!(truth("<>[][FALSE]_x", &[0, 1, 2], 2));
        assert!(!truth("<>[][FALSE]_x", &[0, 1], 0));
        assert!(truth("[][x' >= x]_x", &[0, 1, 2], 2));
        assert!(!truth("[][x' >= x]_x", &[0, 1], 0));
    }

    #[test]
    fn enabled_uses_the_action_successors() {
        assert!(truth("[]<>(~ENABLED Step)", &[0, 1, 2], 2));
        assert!(!truth("[]<>(~ENABLED Step)", &[0, 1], 1));
    }

    #[test]
    fn weak_fairness_on_the_cycle() {
        assert!(!truth("WF_x(Step)", &[0], 0));
        assert!(!truth("WF_x(Step)", &[0, 1], 1));
        assert!(truth("WF_x(Step)", &[0, 1, 2], 2));
    }

    #[test]
    fn strong_versus_weak_fairness_on_intermittent_enabledness() {
        let fixture = Fixture::new();
        let model = fixture.model();
        let action = formula("x = 1 /\\ x' = 2");
        let subscript: Arc<str> = Arc::from("x");
        let flicker = lasso(&[0, 1], 0);
        let weak = Expr::WeakFairness(subscript.clone(), Box::new(action.clone()));
        let strong = Expr::StrongFairness(subscript, Box::new(action));
        assert!(
            model
                .holds(&flicker, &weak, 0, &Env::new())
                .expect("WF evaluates"),
            "on 0,1,0,1,... the action is enabled only at x=1, never continuously, so WF holds"
        );
        assert!(
            !model
                .holds(&flicker, &strong, 0, &Env::new())
                .expect("SF evaluates"),
            "enabled infinitely often and never taken: SF is violated"
        );
    }

    #[test]
    fn pure_stutter_action_is_never_angle_enabled() {
        assert!(truth("WF_x(UNCHANGED x)", &[0], 0));
        assert!(truth("SF_x(UNCHANGED x)", &[0], 0));
    }

    #[test]
    fn subscript_restricts_what_counts_as_taking_the_action() {
        assert!(truth("WF_x(x' = x)", &[0], 0));
        assert!(!truth("WF_x(x' = x + 1)", &[0], 0));
    }

    #[test]
    fn behavior_check_accepts_real_steps_and_stutters() {
        let fixture = Fixture::new();
        let model = fixture.model();
        let init = formula("x = 0");
        let next = fixture
            .defs
            .get("Next")
            .map(|(_, body)| body.as_ref().clone())
            .expect("Next defined");
        assert!(
            model
                .check_is_behavior(&lasso(&[0, 1, 2], 2), &init, &next)
                .is_ok()
        );
        assert!(
            model
                .check_is_behavior(&lasso(&[0, 2], 1), &init, &next)
                .is_err(),
            "0 -> 2 is not a Walk step"
        );
        assert!(
            model
                .check_is_behavior(&lasso(&[1, 2], 1), &init, &next)
                .is_err(),
            "x = 1 is not initial"
        );
        assert!(
            model
                .check_is_behavior(&lasso(&[0, 1], 0), &init, &next)
                .is_err(),
            "the wraparound 1 -> 0 is not a Walk step"
        );
    }
}
