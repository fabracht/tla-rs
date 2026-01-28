use std::io::Write;
use std::sync::Arc;

use indexmap::IndexSet;

use crate::ast::{State, Value};
use crate::checker::format_value;

pub fn export_dot<W: Write>(
    states: &IndexSet<State>,
    parents: &[Option<usize>],
    vars: &[Arc<str>],
    error_state: Option<usize>,
    out: &mut W,
) -> std::io::Result<()> {
    writeln!(out, "digraph StateGraph {{")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(out, "  node [shape=box, fontname=\"monospace\"];")?;

    for (idx, state) in states.iter().enumerate() {
        let label = format_state_label(state, vars);
        let style = if Some(idx) == error_state {
            ", color=red, penwidth=2"
        } else {
            ""
        };
        writeln!(out, "  s{} [label=\"{}\"{}];", idx, label, style)?;
    }

    for (idx, parent) in parents.iter().enumerate() {
        if let Some(p) = parent {
            writeln!(out, "  s{} -> s{};", p, idx)?;
        }
    }

    writeln!(out, "}}")?;
    Ok(())
}

fn format_state_label(state: &State, vars: &[Arc<str>]) -> String {
    vars.iter()
        .enumerate()
        .filter_map(|(i, v)| state.values.get(i).map(|val| format!("{}={}", v, format_value_escaped(val))))
        .collect::<Vec<_>>()
        .join("\\n")
}

fn format_value_escaped(val: &Value) -> String {
    format_value(val)
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
}
