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

struct TarjanState {
    index: usize,
    indices: Vec<Option<usize>>,
    lowlinks: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    sccs: Vec<SCC>,
}

impl TarjanState {
    fn new(node_count: usize) -> Self {
        Self {
            index: 0,
            indices: vec![None; node_count],
            lowlinks: vec![0; node_count],
            on_stack: vec![false; node_count],
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }
}

pub fn compute_sccs(graph: &StateGraph) -> Vec<SCC> {
    let node_count = graph.state_count();
    if node_count == 0 {
        return Vec::new();
    }

    let mut state = TarjanState::new(node_count);

    for v in 0..node_count {
        if state.indices[v].is_none() {
            strongconnect(graph, v, &mut state);
        }
    }

    state.sccs
}

fn strongconnect(graph: &StateGraph, v: usize, state: &mut TarjanState) {
    state.indices[v] = Some(state.index);
    state.lowlinks[v] = state.index;
    state.index += 1;
    state.stack.push(v);
    state.on_stack[v] = true;

    for edge in graph.successors(v) {
        let w = edge.target;
        if state.indices[w].is_none() {
            strongconnect(graph, w, state);
            state.lowlinks[v] = state.lowlinks[v].min(state.lowlinks[w]);
        } else if state.on_stack[w] {
            state.lowlinks[v] = state.lowlinks[v].min(state.indices[w].unwrap());
        }
    }

    if state.lowlinks[v] == state.indices[v].unwrap() {
        let mut scc_states = Vec::new();
        loop {
            let w = state.stack.pop().unwrap();
            state.on_stack[w] = false;
            scc_states.push(w);
            if w == v {
                break;
            }
        }

        let is_trivial = scc_states.len() == 1 && !has_self_loop(graph, scc_states[0]);
        state.sccs.push(SCC::new(scc_states, is_trivial));
    }
}

fn has_self_loop(graph: &StateGraph, v: usize) -> bool {
    graph.successors(v).iter().any(|e| e.target == v)
}

pub fn get_nontrivial_sccs(graph: &StateGraph) -> Vec<SCC> {
    compute_sccs(graph)
        .into_iter()
        .filter(|scc| !scc.is_trivial)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{State, Value};
    use crate::graph::StateGraph;
    use std::sync::Arc;

    fn state_with_x(n: i64) -> State {
        let mut s = State::new();
        s.vars.insert(Arc::from("x"), Value::Int(n));
        s
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
        assert!(nontrivial[0].states.len() == 2);
    }
}
