//! The Manna–Pnueli tableau of a temporal formula, as TLC builds it.
//!
//! A node is a fully expanded set of subformulas that can hold at one position of a
//! behavior: conjunctions are split, disjunctions branch, `[]F` holds `F` now and
//! again next, and `<>F` either holds `F` now or is deferred to the next position.
//! What must hold now is the node's literals; what must hold next is expanded again
//! into its successors. A behavior satisfies the formula exactly when it has a run
//! through the tableau, starting at an initial node, that honors every literal and
//! whose infinitely repeated nodes fulfill every eventuality: for each `<>F`, some
//! repeated node either does not contain `<>F` or contains `F`.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ltl::{Literal, Ltl};

/// Past this many nodes a formula is too large to check.
const MAX_NODES: usize = 4096;

/// Past this many expansion steps for one set of formulas, it is too large to check:
/// a formula within the node cap needs far fewer, so the budget only stops formulas
/// whose expansion would otherwise run for exponential time before the cap is seen.
const MAX_EXPANSION_STEPS: usize = 1 << 24;

fn too_large() -> String {
    format!("the temporal formula needs more than {MAX_NODES} tableau nodes")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableauNode {
    /// What the node requires at its position: state literals of the current state,
    /// step literals of the transition to the next position.
    pub literals: Vec<Literal>,
    pub successors: Vec<usize>,
    /// `fulfills[k]` holds when the node discharges the `k`-th eventuality.
    pub fulfills: Vec<bool>,
}

#[derive(Debug, Clone)]
pub struct Tableau {
    pub nodes: Vec<TableauNode>,
    pub initial: Vec<usize>,
    pub eventualities: usize,
}

type FormulaSet = BTreeSet<usize>;

struct Closure {
    formulas: Vec<Ltl>,
    ids: HashMap<Ltl, usize>,
}

impl Closure {
    fn id(&mut self, formula: &Ltl) -> usize {
        if let Some(&id) = self.ids.get(formula) {
            return id;
        }
        let id = self.formulas.len();
        self.formulas.push(formula.clone());
        self.ids.insert(formula.clone(), id);
        id
    }
}

/// One way of satisfying a set of formulas at a position: the subformulas that
/// hold there, and the formulas that must hold at the next position.
#[derive(Default, Clone)]
struct Branch {
    pending: Vec<usize>,
    current: FormulaSet,
    literals: BTreeSet<Literal>,
    next: FormulaSet,
}

pub fn build(formula: &Ltl) -> Result<Tableau, String> {
    let mut closure = Closure {
        formulas: Vec::new(),
        ids: HashMap::new(),
    };
    let root = closure.id(formula);
    let mut eventualities: Vec<(usize, usize)> = Vec::new();
    collect_eventualities(formula, &mut closure, &mut eventualities);

    let mut nodes: Vec<TableauNode> = Vec::new();
    let mut index: HashMap<(FormulaSet, FormulaSet), usize> = HashMap::new();
    let mut frontier: Vec<(usize, FormulaSet)> = Vec::new();

    let mut intern = |branch: Branch,
                      nodes: &mut Vec<TableauNode>,
                      frontier: &mut Vec<(usize, FormulaSet)>|
     -> Result<usize, String> {
        let key = (branch.current.clone(), branch.next.clone());
        if let Some(&id) = index.get(&key) {
            return Ok(id);
        }
        if nodes.len() >= MAX_NODES {
            return Err(too_large());
        }
        let id = nodes.len();
        nodes.push(TableauNode {
            literals: branch.literals.iter().copied().collect(),
            successors: Vec::new(),
            fulfills: eventualities
                .iter()
                .map(|&(eventuality, body)| {
                    !branch.current.contains(&eventuality) || branch.current.contains(&body)
                })
                .collect(),
        });
        index.insert(key, id);
        frontier.push((id, branch.next));
        Ok(id)
    };

    let mut initial = Vec::new();
    for branch in expand(&[root], &mut closure)? {
        initial.push(intern(branch, &mut nodes, &mut frontier)?);
    }
    let mut expanded: HashMap<FormulaSet, Vec<usize>> = HashMap::new();
    while let Some((id, next)) = frontier.pop() {
        let successors = match expanded.get(&next) {
            Some(successors) => successors.clone(),
            None => {
                let pending: Vec<usize> = next.iter().copied().collect();
                let mut successors = Vec::new();
                for branch in expand(&pending, &mut closure)? {
                    successors.push(intern(branch, &mut nodes, &mut frontier)?);
                }
                expanded.insert(next, successors.clone());
                successors
            }
        };
        nodes[id].successors = successors;
    }
    Ok(Tableau {
        nodes,
        initial,
        eventualities: eventualities.len(),
    })
}

fn collect_eventualities(formula: &Ltl, closure: &mut Closure, out: &mut Vec<(usize, usize)>) {
    match formula {
        Ltl::True | Ltl::False | Ltl::Literal(_) => {}
        Ltl::And(parts) | Ltl::Or(parts) => {
            for part in parts {
                collect_eventualities(part, closure, out);
            }
        }
        Ltl::Always(inner) => collect_eventualities(inner, closure, out),
        Ltl::Eventually(inner) => {
            let pair = (closure.id(formula), closure.id(inner));
            if !out.contains(&pair) {
                out.push(pair);
            }
            collect_eventualities(inner, closure, out);
        }
    }
}

/// Every distinct consistent way of satisfying all of `formulas` at one position,
/// each a different node. Stops with an error as soon as there are more of them than
/// the tableau may hold, or the expansion exceeds its step budget, rather than first
/// enumerating every combination of an oversized formula.
fn expand(formulas: &[usize], closure: &mut Closure) -> Result<Vec<Branch>, String> {
    let mut done = Vec::new();
    let mut seen: HashSet<(FormulaSet, FormulaSet)> = HashSet::new();
    let mut steps = 0usize;
    let mut work = vec![Branch {
        pending: formulas.to_vec(),
        ..Branch::default()
    }];
    while let Some(mut branch) = work.pop() {
        steps += 1;
        if steps > MAX_EXPANSION_STEPS {
            return Err(too_large());
        }
        let Some(id) = branch.pending.pop() else {
            if seen.insert((branch.current.clone(), branch.next.clone())) {
                if seen.len() > MAX_NODES {
                    return Err(too_large());
                }
                done.push(branch);
            }
            continue;
        };
        if branch.current.contains(&id) {
            work.push(branch);
            continue;
        }
        let formula = closure.formulas[id].clone();
        match formula {
            Ltl::True => {
                branch.current.insert(id);
                work.push(branch);
            }
            Ltl::False => {}
            Ltl::Literal(literal) => {
                let opposite = Literal {
                    positive: !literal.positive,
                    ..literal
                };
                if !branch.literals.contains(&opposite) {
                    branch.current.insert(id);
                    branch.literals.insert(literal);
                    work.push(branch);
                }
            }
            Ltl::And(parts) => {
                branch.current.insert(id);
                for part in &parts {
                    branch.pending.push(closure.id(part));
                }
                work.push(branch);
            }
            Ltl::Or(parts) => {
                branch.current.insert(id);
                let alternatives: BTreeSet<usize> = parts.iter().map(|p| closure.id(p)).collect();
                for part in alternatives {
                    let mut alternative = branch.clone();
                    alternative.pending.push(part);
                    work.push(alternative);
                }
            }
            Ltl::Always(inner) => {
                branch.current.insert(id);
                branch.next.insert(id);
                branch.pending.push(closure.id(&inner));
                work.push(branch);
            }
            Ltl::Eventually(inner) => {
                branch.current.insert(id);
                let mut now = branch.clone();
                now.pending.push(closure.id(&inner));
                work.push(now);
                branch.next.insert(id);
                work.push(branch);
            }
        }
    }
    Ok(done)
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::graph::LivenessGraph;

    const STATE_ATOMS: usize = 2;
    const STEP_ATOM: usize = 2;

    /// A lasso over valuations: `state[i][a]` is state atom `a` at position `i`,
    /// `step[i]` the step atom on the transition out of `i`; after the last
    /// position the behavior returns to `loop_start`.
    struct Lasso {
        state: Vec<[bool; STATE_ATOMS]>,
        step: Vec<bool>,
        loop_start: usize,
    }

    impl Lasso {
        fn len(&self) -> usize {
            self.state.len()
        }

        fn succ(&self, position: usize) -> usize {
            if position + 1 == self.len() {
                self.loop_start
            } else {
                position + 1
            }
        }

        fn literal(&self, literal: Literal, position: usize) -> bool {
            let value = if literal.atom == STEP_ATOM {
                self.step[position]
            } else {
                self.state[position][literal.atom]
            };
            value == literal.positive
        }

        fn holds(&self, formula: &Ltl, position: usize) -> bool {
            match formula {
                Ltl::True => true,
                Ltl::False => false,
                Ltl::Literal(literal) => self.literal(*literal, position),
                Ltl::And(parts) => parts.iter().all(|p| self.holds(p, position)),
                Ltl::Or(parts) => parts.iter().any(|p| self.holds(p, position)),
                Ltl::Always(inner) => self.suffix(position).all(|j| self.holds(inner, j)),
                Ltl::Eventually(inner) => self.suffix(position).any(|j| self.holds(inner, j)),
            }
        }

        /// The positions visited from `position` on: the rest of the prefix and the
        /// whole loop, or only the loop once inside it.
        fn suffix(&self, position: usize) -> std::ops::Range<usize> {
            position.min(self.loop_start)..self.len()
        }
    }

    /// The runs of the tableau over the lasso: node `position * n + t` pairs a
    /// lasso position with tableau node `t` whose literals hold there.
    struct Runs<'a> {
        lasso: &'a Lasso,
        tableau: &'a Tableau,
    }

    impl Runs<'_> {
        fn consistent(&self, position: usize, node: usize) -> bool {
            self.tableau.nodes[node]
                .literals
                .iter()
                .all(|&l| self.lasso.literal(l, position))
        }

        fn split(&self, pair: usize) -> (usize, usize) {
            let n = self.tableau.nodes.len();
            (pair / n, pair % n)
        }

        fn successors(&self, pair: usize) -> Vec<usize> {
            let (position, node) = self.split(pair);
            if !self.consistent(position, node) {
                return Vec::new();
            }
            let next = self.lasso.succ(position);
            self.tableau.nodes[node]
                .successors
                .iter()
                .filter(|&&t| self.consistent(next, t))
                .map(|&t| next * self.tableau.nodes.len() + t)
                .collect()
        }

        fn accepts(&self) -> bool {
            let n = self.tableau.nodes.len();
            let mut reached: HashSet<usize> = self
                .tableau
                .initial
                .iter()
                .filter(|&&t| self.consistent(0, t))
                .copied()
                .collect();
            let mut work: Vec<usize> = reached.iter().copied().collect();
            while let Some(pair) = work.pop() {
                for successor in self.successors(pair) {
                    if reached.insert(successor) {
                        work.push(successor);
                    }
                }
            }
            crate::scc::sccs_within(self, &reached)
                .into_iter()
                .filter(|scc| !scc.is_trivial)
                .any(|scc| {
                    (0..self.tableau.eventualities).all(|k| {
                        scc.states
                            .iter()
                            .any(|&pair| self.tableau.nodes[pair % n].fulfills[k])
                    })
                })
        }
    }

    impl LivenessGraph for Runs<'_> {
        fn node_count(&self) -> usize {
            self.lasso.len() * self.tableau.nodes.len()
        }

        fn edges(&self, node: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
            self.successors(node)
                .into_iter()
                .enumerate()
                .map(|(i, t)| (t, i))
        }

        fn edge(&self, node: usize, index: usize) -> Option<(usize, usize)> {
            self.successors(node).get(index).map(|&t| (t, index))
        }

        fn state_of(&self, node: usize) -> usize {
            self.split(node).0
        }
    }

    fn literal(atom: usize, positive: bool) -> Ltl {
        Ltl::Literal(Literal { atom, positive })
    }

    fn random_formula(rng: &mut fastrand::Rng, depth: usize) -> Ltl {
        let leaf = depth == 0 || rng.u8(0..4) == 0;
        if leaf {
            return match rng.u8(0..10) {
                0 => Ltl::True,
                1 => Ltl::False,
                _ => literal(rng.usize(0..=STEP_ATOM), rng.bool()),
            };
        }
        let sub = |rng: &mut fastrand::Rng| random_formula(rng, depth - 1);
        match rng.u8(0..4) {
            0 => Ltl::And(vec![sub(rng), sub(rng)]),
            1 => Ltl::Or(vec![sub(rng), sub(rng)]),
            2 => Ltl::Always(Box::new(sub(rng))),
            _ => Ltl::Eventually(Box::new(sub(rng))),
        }
    }

    fn random_lasso(rng: &mut fastrand::Rng) -> Lasso {
        let len = rng.usize(1..6);
        Lasso {
            state: (0..len).map(|_| [rng.bool(), rng.bool()]).collect(),
            step: (0..len).map(|_| rng.bool()).collect(),
            loop_start: rng.usize(0..len),
        }
    }

    #[test]
    fn tableau_accepts_exactly_the_lassos_that_satisfy_the_formula() {
        let mut rng = fastrand::Rng::with_seed(0x7AB1EA);
        for trial in 0..3000 {
            let formula = random_formula(&mut rng, 4);
            let tableau = build(&formula).expect("small formulas fit");
            for _ in 0..8 {
                let lasso = random_lasso(&mut rng);
                let runs = Runs {
                    lasso: &lasso,
                    tableau: &tableau,
                };
                assert_eq!(
                    runs.accepts(),
                    lasso.holds(&formula, 0),
                    "trial {trial}: {formula:?} on {:?} / {:?} looping to {}",
                    lasso.state,
                    lasso.step,
                    lasso.loop_start
                );
            }
        }
    }

    #[test]
    fn eventuality_is_tracked_until_fulfilled() {
        let p = literal(0, true);
        let tableau = build(&Ltl::Eventually(Box::new(p))).unwrap();
        assert_eq!(tableau.eventualities, 1);
        assert!(
            tableau
                .nodes
                .iter()
                .any(|n| !n.fulfills[0] && n.literals.is_empty()),
            "a node that defers <>p leaves it unfulfilled"
        );
    }

    #[test]
    fn contradictory_literals_have_no_node() {
        let formula = Ltl::And(vec![literal(0, true), literal(0, false)]);
        assert!(build(&formula).unwrap().initial.is_empty());
    }

    #[test]
    fn oversized_formula_is_an_error() {
        let many = Ltl::And(
            (0..14)
                .map(|atom| Ltl::Eventually(Box::new(literal(atom, true))))
                .collect(),
        );
        let error = build(&many).expect_err("2^14 eventuality combinations exceed the cap");
        assert!(error.contains("tableau nodes"), "{error}");
    }

    #[test]
    fn many_eventualities_stop_at_the_cap_without_enumerating_them() {
        let many = Ltl::And(
            (0..30)
                .map(|atom| Ltl::Eventually(Box::new(literal(atom, true))))
                .collect(),
        );
        let error = build(&many).expect_err("2^30 distinct nodes exceed the cap");
        assert!(error.contains("tableau nodes"), "{error}");
    }

    #[test]
    fn repeated_alternatives_do_not_multiply_branches() {
        let repeated = Ltl::And(
            (0..40)
                .map(|atom| Ltl::Or(vec![literal(atom, true), literal(atom, true)]))
                .collect(),
        );
        let tableau = build(&repeated).expect("each disjunction has one distinct alternative");
        assert_eq!(tableau.initial.len(), 1);
    }

    #[test]
    fn converging_disjunctions_within_the_cap_are_built_correctly() {
        let shared = Ltl::Or(vec![literal(0, true), literal(1, true)]);
        let formula = Ltl::Always(Box::new(Ltl::And(
            (0..6)
                .map(|_| Ltl::Or(vec![literal(STEP_ATOM, true), shared.clone()]))
                .chain([Ltl::Eventually(Box::new(literal(0, false)))])
                .collect(),
        )));
        let tableau = build(&formula).expect("the distinct nodes fit the cap");
        let mut rng = fastrand::Rng::with_seed(0xC0DE);
        for _ in 0..200 {
            let lasso = random_lasso(&mut rng);
            let runs = Runs {
                lasso: &lasso,
                tableau: &tableau,
            };
            assert_eq!(runs.accepts(), lasso.holds(&formula, 0));
        }
    }

    #[test]
    fn conjunction_of_recurrences_builds_within_the_cap() {
        let recurring = Ltl::And(
            (0..8)
                .map(|atom| Ltl::Always(Box::new(Ltl::Eventually(Box::new(literal(atom, true))))))
                .collect(),
        );
        let tableau = build(&recurring).expect("256 eventuality combinations fit the cap");
        assert!(tableau.nodes.len() <= 4096);
        assert!(tableau.nodes.iter().all(|n| !n.successors.is_empty()));
    }
}
