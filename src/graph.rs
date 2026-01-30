use std::sync::Arc;

use indexmap::IndexSet;

use crate::ast::State;

#[derive(Debug, Clone)]
pub struct Edge {
    pub target: usize,
    pub action: Option<Arc<str>>,
}

pub struct StateGraph {
    pub states: IndexSet<State>,
    pub edges: Vec<Vec<Edge>>,
    pub parents: Vec<Option<usize>>,
}

impl StateGraph {
    pub fn new() -> Self {
        Self {
            states: IndexSet::new(),
            edges: Vec::new(),
            parents: Vec::new(),
        }
    }

    pub fn add_state(&mut self, state: State, parent: Option<usize>) -> (usize, bool) {
        let (idx, is_new) = self.states.insert_full(state);
        if is_new {
            self.parents.push(parent);
            self.edges.push(Vec::new());
        }
        (idx, is_new)
    }

    pub fn add_edge(&mut self, from: usize, to: usize, action: Option<Arc<str>>) {
        if from < self.edges.len() {
            self.edges[from].push(Edge { target: to, action });
        }
    }

    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    pub fn edge_count(&self) -> usize {
        self.edges.iter().map(|e| e.len()).sum()
    }

    pub fn get_state(&self, idx: usize) -> Option<&State> {
        self.states.get_index(idx)
    }

    pub fn reconstruct_trace(&self, state_idx: usize) -> Vec<State> {
        let mut trace = Vec::new();
        let mut idx = Some(state_idx);
        while let Some(i) = idx {
            if let Some(state) = self.states.get_index(i) {
                trace.push(state.clone());
            }
            idx = self.parents.get(i).copied().flatten();
        }
        trace.reverse();
        trace
    }

    pub fn successors(&self, idx: usize) -> &[Edge] {
        self.edges.get(idx).map(|v| v.as_slice()).unwrap_or(&[])
    }

    pub fn outgoing_edges(&self, idx: usize) -> impl Iterator<Item = &Edge> {
        self.edges.get(idx).into_iter().flat_map(|v| v.iter())
    }

    pub fn has_edge_with_action(&self, idx: usize, action_name: &str) -> bool {
        self.outgoing_edges(idx)
            .any(|e| e.action.as_ref().is_some_and(|a| a.as_ref() == action_name))
    }
}

impl Default for StateGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{State, Value};

    fn state_with_x(n: i64) -> State {
        State {
            values: vec![Value::Int(n)],
        }
    }

    #[test]
    fn graph_basic_operations() {
        let mut graph = StateGraph::new();

        let s0 = state_with_x(0);
        let (idx0, is_new0) = graph.add_state(s0, None);
        assert_eq!(idx0, 0);
        assert!(is_new0);

        let s1 = state_with_x(1);
        let (idx1, is_new1) = graph.add_state(s1, Some(0));
        assert_eq!(idx1, 1);
        assert!(is_new1);

        graph.add_edge(0, 1, Some("Inc".into()));

        assert_eq!(graph.state_count(), 2);
        assert_eq!(graph.edge_count(), 1);
        assert!(graph.has_edge_with_action(0, "Inc"));
        assert!(!graph.has_edge_with_action(0, "Dec"));
    }

    #[test]
    fn trace_reconstruction() {
        let mut graph = StateGraph::new();

        graph.add_state(state_with_x(0), None);
        graph.add_state(state_with_x(1), Some(0));
        graph.add_state(state_with_x(2), Some(1));

        let trace = graph.reconstruct_trace(2);
        assert_eq!(trace.len(), 3);
    }
}
