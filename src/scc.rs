use std::collections::HashSet;

use crate::graph::StateGraph;

#[derive(Debug, Clone)]
pub struct SCC {
    pub states: Vec<usize>,
    pub is_trivial: bool,
}

impl SCC {
    pub fn new(states: Vec<usize>, is_trivial: bool) -> Self {
        Self { states, is_trivial }
    }

    pub fn contains(&self, state: usize) -> bool {
        self.states.contains(&state)
    }
}

/// Strongly connected components of the whole graph.
pub fn compute_sccs(graph: &StateGraph) -> Vec<SCC> {
    tarjan(graph, |_| true)
}

/// The components that contain a cycle: more than one state, or a self-loop.
pub fn get_nontrivial_sccs(graph: &StateGraph) -> Vec<SCC> {
    compute_sccs(graph)
        .into_iter()
        .filter(|scc| !scc.is_trivial)
        .collect()
}

/// Strongly connected components of the subgraph induced by `allowed`.
pub fn compute_sccs_in_subset(graph: &StateGraph, allowed: &HashSet<usize>) -> Vec<SCC> {
    if allowed.is_empty() {
        return Vec::new();
    }
    tarjan(graph, |state| allowed.contains(&state))
}

/// Tarjan's algorithm over the states for which `allowed` holds, with an explicit
/// stack of `(state, next edge)` frames instead of recursion, so the depth of the
/// search is bounded by memory rather than by the thread's stack. Components come
/// out in the same order as the recursive formulation: reverse topological order.
/// A single-state component is trivial unless it has a self-loop.
fn tarjan(graph: &StateGraph, allowed: impl Fn(usize) -> bool) -> Vec<SCC> {
    let node_count = graph.state_count();
    let mut index = vec![usize::MAX; node_count];
    let mut lowlink = vec![0; node_count];
    let mut on_stack = vec![false; node_count];
    let mut component_stack: Vec<usize> = Vec::new();
    let mut frames: Vec<(usize, usize)> = Vec::new();
    let mut next_index = 0;
    let mut sccs = Vec::new();

    for root in 0..node_count {
        if index[root] != usize::MAX || !allowed(root) {
            continue;
        }
        index[root] = next_index;
        lowlink[root] = next_index;
        next_index += 1;
        component_stack.push(root);
        on_stack[root] = true;
        frames.push((root, 0));

        while let Some(&mut (v, ref mut next_edge)) = frames.last_mut() {
            let edges = graph.successors(v);
            if let Some(edge) = edges.get(*next_edge) {
                *next_edge += 1;
                let w = edge.target;
                if !allowed(w) {
                    continue;
                }
                if index[w] == usize::MAX {
                    index[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    component_stack.push(w);
                    on_stack[w] = true;
                    frames.push((w, 0));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
                continue;
            }

            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                lowlink[parent] = lowlink[parent].min(lowlink[v]);
            }
            if lowlink[v] == index[v] {
                let mut states = Vec::new();
                while let Some(w) = component_stack.pop() {
                    on_stack[w] = false;
                    states.push(w);
                    if w == v {
                        break;
                    }
                }
                let is_trivial =
                    states.len() == 1 && !graph.successors(v).iter().any(|e| e.target == v);
                sccs.push(SCC::new(states, is_trivial));
            }
        }
    }

    sccs
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::ast::{State, Value};
    use crate::graph::StateGraph;

    fn state_with_x(n: i64) -> State {
        State {
            values: vec![Value::Int(n)],
        }
    }

    #[test]
    fn simple_cycle() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_state(state_with_x(2), Some(1));

        graph.add_edge(0, 1, None);
        graph.add_edge(1, 2, None);
        graph.add_edge(2, 0, None);

        let sccs = compute_sccs(&graph);
        assert_eq!(sccs.len(), 1);
        assert!(!sccs[0].is_trivial);
        assert_eq!(sccs[0].states.len(), 3);
    }

    #[test]
    fn no_cycle() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_state(state_with_x(2), Some(1));

        graph.add_edge(0, 1, None);
        graph.add_edge(1, 2, None);

        let sccs = compute_sccs(&graph);
        assert_eq!(sccs.len(), 3);
        assert!(sccs.iter().all(|scc| scc.is_trivial));
    }

    #[test]
    fn self_loop() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_edge(0, 0, None);

        let sccs = compute_sccs(&graph);
        assert_eq!(sccs.len(), 1);
        assert!(!sccs[0].is_trivial);
    }

    #[test]
    fn multiple_sccs() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_state(state_with_x(2), None);
        graph.add_state(state_with_x(3), Some(2));

        graph.add_edge(0, 1, None);
        graph.add_edge(1, 0, None);
        graph.add_edge(0, 2, None);
        graph.add_edge(2, 3, None);
        graph.add_edge(3, 2, None);

        let sccs = compute_sccs(&graph);
        let nontrivial: Vec<_> = sccs.iter().filter(|s| !s.is_trivial).collect();
        assert_eq!(nontrivial.len(), 2);
    }

    #[test]
    fn nontrivial_filter() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_state(state_with_x(2), Some(1));

        graph.add_edge(0, 1, None);
        graph.add_edge(1, 2, None);
        graph.add_edge(2, 1, None);

        let nontrivial = get_nontrivial_sccs(&graph);
        assert_eq!(nontrivial.len(), 1);
        assert!(nontrivial[0].contains(1) && nontrivial[0].contains(2));
        assert!(!nontrivial[0].contains(0));
        assert!(nontrivial[0].states.len() == 2);
    }

    fn chain(len: usize, closing_edge: bool) -> StateGraph {
        let mut graph = StateGraph::new();
        for i in 0..len {
            graph.add_state(state_with_x(i as i64), i.checked_sub(1));
        }
        for i in 1..len {
            graph.add_edge(i - 1, i, None);
        }
        if closing_edge {
            graph.add_edge(len - 1, 0, None);
        }
        graph
    }

    #[test]
    fn deep_chain_does_not_exhaust_the_stack() {
        let open = compute_sccs(&chain(500_000, false));
        assert_eq!(open.len(), 500_000);
        assert!(open.iter().all(|scc| scc.is_trivial));
        let closed = compute_sccs(&chain(500_000, true));
        assert_eq!(closed.len(), 1);
        assert_eq!(closed[0].states.len(), 500_000);
    }

    #[test]
    fn subset_ignores_states_and_edges_outside_it() {
        let graph = chain(6, true);
        let allowed: HashSet<usize> = [1, 2, 3].into_iter().collect();
        let sccs = compute_sccs_in_subset(&graph, &allowed);
        assert_eq!(sccs.len(), 3, "the cycle is broken by the excluded states");
        assert!(sccs.iter().all(|scc| scc.is_trivial));
        let mut covered: Vec<usize> = sccs.iter().flat_map(|scc| scc.states.clone()).collect();
        covered.sort_unstable();
        assert_eq!(covered, vec![1, 2, 3]);
    }

    fn reaches(graph: &StateGraph, allowed: &HashSet<usize>, from: usize, to: usize) -> bool {
        let mut seen = HashSet::from([from]);
        let mut work = vec![from];
        while let Some(v) = work.pop() {
            if v == to {
                return true;
            }
            for edge in graph.successors(v) {
                if allowed.contains(&edge.target) && seen.insert(edge.target) {
                    work.push(edge.target);
                }
            }
        }
        false
    }

    #[test]
    fn components_match_mutual_reachability_on_random_graphs() {
        let mut rng = fastrand::Rng::with_seed(0x5CC);
        for _ in 0..300 {
            let n = rng.usize(1..14);
            let mut graph = StateGraph::new();
            for i in 0..n {
                graph.add_state(state_with_x(i as i64), None);
            }
            for _ in 0..rng.usize(0..3 * n) {
                graph.add_edge(rng.usize(0..n), rng.usize(0..n), None);
            }
            let allowed: HashSet<usize> = (0..n).filter(|_| rng.u8(0..4) > 0).collect();
            let sccs = compute_sccs_in_subset(&graph, &allowed);
            let mut component_of = vec![usize::MAX; n];
            for (id, scc) in sccs.iter().enumerate() {
                for &s in &scc.states {
                    assert_eq!(component_of[s], usize::MAX, "state {s} in two components");
                    component_of[s] = id;
                }
                let cyclic = scc.states.len() > 1
                    || graph
                        .successors(scc.states[0])
                        .iter()
                        .any(|e| e.target == scc.states[0]);
                assert_eq!(scc.is_trivial, !cyclic);
            }
            for a in 0..n {
                assert_eq!(component_of[a] != usize::MAX, allowed.contains(&a));
                for b in 0..n {
                    if allowed.contains(&a) && allowed.contains(&b) {
                        let mutual =
                            reaches(&graph, &allowed, a, b) && reaches(&graph, &allowed, b, a);
                        assert_eq!(component_of[a] == component_of[b], mutual, "{a} {b}");
                    }
                }
            }
        }
    }
}
