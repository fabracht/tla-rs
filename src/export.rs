use std::collections::HashSet;
use std::io::Write;
use std::sync::Arc;

use indexmap::IndexSet;

use crate::ast::{State, Value};
use crate::checker::{StateMetadata, format_value};

/// Finds the edges that can be reached through `via` fields in the StateMetadata to
/// the error state. The nodes visited with BSF include also other nodes that didn't
/// result in error.
fn collect_error_trace_edges(
    metadata: &[StateMetadata],
    error_state: Option<usize>,
) -> HashSet<(usize, usize)> {
    let mut edges = HashSet::new();
    let mut current = error_state;
    while let Some(idx) = current {
        if let Some(meta) = metadata.get(idx) {
            if let Some(via) = &meta.via {
                edges.insert((via.state_idx, idx));
                current = Some(via.state_idx);
            } else {
                current = None;
            }
        } else {
            current = None;
        }
    }
    edges
}

pub fn export_dot<W: Write>(
    states: &IndexSet<State>,
    metadata: &[StateMetadata],
    vars: &[Arc<str>],
    error_state: Option<usize>,
    out: &mut W,
) -> std::io::Result<()> {
    writeln!(out, "digraph StateGraph {{")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(out, "  node [shape=box, fontname=\"monospace\"];")?;

    let trace_edges = collect_error_trace_edges(metadata, error_state);

    for (idx, state) in states.iter().enumerate() {
        let label = format_state_label(state, vars);
        let style = if Some(idx) == error_state {
            ", color=red, penwidth=2"
        } else {
            ""
        };
        writeln!(out, "  s{} [label=\"{}\"{}];", idx, label, style)?;
    }

    for (idx, meta) in metadata.iter().enumerate() {
        for succ in &meta.successors {
            let is_trace_edge = trace_edges.contains(&(idx, *succ));

            let attributes = if is_trace_edge {
                " [penwidth=3.0, color=\"black\"]"
            } else {
                " [color=\"gray50\"]"
            };

            writeln!(out, "  s{} -> s{}{};", idx, succ, attributes)?;
        }
    }

    writeln!(out, "}}")?;
    Ok(())
}

fn format_state_label(state: &State, vars: &[Arc<str>]) -> String {
    vars.iter()
        .enumerate()
        .filter_map(|(i, v)| {
            state
                .values
                .get(i)
                .map(|val| format!("{}={}", v, format_value_escaped(val)))
        })
        .collect::<Vec<_>>()
        .join("\\n")
}

fn format_value_escaped(val: &Value) -> String {
    format_value(val).replace('\\', "\\\\").replace('"', "\\\"")
}
