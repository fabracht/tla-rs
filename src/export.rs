use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::io::Write;
use std::str::FromStr;
use std::sync::Arc;

use indexmap::IndexSet;

use crate::ast::{State, Value};
use crate::checker::format_value;

pub type EdgeList = Vec<(usize, Option<Arc<str>>)>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DotMode {
    Full,
    Trace,
    #[default]
    Clean,
    Choices,
}

impl FromStr for DotMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "full" => Ok(DotMode::Full),
            "trace" => Ok(DotMode::Trace),
            "clean" => Ok(DotMode::Clean),
            "choices" => Ok(DotMode::Choices),
            other => Err(format!(
                "unknown dot mode '{}' (expected: full, trace, clean, choices)",
                other
            )),
        }
    }
}

impl fmt::Display for DotMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DotMode::Full => write!(f, "full"),
            DotMode::Trace => write!(f, "trace"),
            DotMode::Clean => write!(f, "clean"),
            DotMode::Choices => write!(f, "choices"),
        }
    }
}

pub struct DotExport<'a> {
    pub states: &'a IndexSet<State>,
    pub parents: &'a [Option<usize>],
    pub vars: &'a [Arc<str>],
    pub error_state: Option<usize>,
    pub all_edges: &'a [EdgeList],
    pub trace_path: &'a [usize],
    pub mode: DotMode,
}

pub fn export_dot<W: Write>(ctx: &DotExport<'_>, out: &mut W) -> std::io::Result<()> {
    match ctx.mode {
        DotMode::Full => render_full_mode(
            ctx.states,
            ctx.parents,
            ctx.vars,
            ctx.error_state,
            ctx.all_edges,
            ctx.trace_path,
            out,
        ),
        DotMode::Trace => {
            if ctx.trace_path.is_empty() {
                render_full_mode(
                    ctx.states,
                    ctx.parents,
                    ctx.vars,
                    ctx.error_state,
                    ctx.all_edges,
                    ctx.trace_path,
                    out,
                )
            } else {
                render_trace_mode(
                    ctx.states,
                    ctx.vars,
                    ctx.error_state,
                    ctx.all_edges,
                    ctx.trace_path,
                    out,
                )
            }
        }
        DotMode::Clean => render_clean_mode(
            ctx.states,
            ctx.parents,
            ctx.vars,
            ctx.error_state,
            ctx.all_edges,
            ctx.trace_path,
            out,
        ),
        DotMode::Choices => {
            if ctx.trace_path.is_empty() {
                render_full_mode(
                    ctx.states,
                    ctx.parents,
                    ctx.vars,
                    ctx.error_state,
                    ctx.all_edges,
                    ctx.trace_path,
                    out,
                )
            } else {
                render_choices_mode(
                    ctx.states,
                    ctx.vars,
                    ctx.error_state,
                    ctx.all_edges,
                    ctx.trace_path,
                    out,
                )
            }
        }
    }
}

fn write_header<W: Write>(out: &mut W) -> std::io::Result<()> {
    writeln!(out, "digraph StateGraph {{")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(out, "  node [shape=box, fontname=\"monospace\"];")
}

fn build_trace_sets(trace_path: &[usize]) -> (HashSet<usize>, HashSet<(usize, usize)>) {
    let trace_nodes: HashSet<usize> = trace_path.iter().copied().collect();
    let trace_edges: HashSet<(usize, usize)> =
        trace_path.windows(2).map(|w| (w[0], w[1])).collect();
    (trace_nodes, trace_edges)
}

fn node_style(
    idx: usize,
    error_state: Option<usize>,
    trace_nodes: &HashSet<usize>,
) -> &'static str {
    if Some(idx) == error_state {
        ", color=red, penwidth=2, style=filled, fillcolor=\"#ffcccc\""
    } else if trace_nodes.contains(&idx) {
        ", color=red, penwidth=2"
    } else {
        ""
    }
}

fn write_node<W: Write>(out: &mut W, idx: usize, label: &str, style: &str) -> std::io::Result<()> {
    writeln!(out, "  s{} [label=\"{}\"{}];", idx, label, style)
}

fn escape_edge_label(label: &Arc<str>) -> String {
    label.replace('\\', "\\\\").replace('"', "\\\"")
}

fn find_edge_label(all_edges: &[EdgeList], src: usize, dst: usize) -> Option<&Arc<str>> {
    all_edges.get(src).and_then(|edges| {
        edges
            .iter()
            .find_map(|(d, action)| if *d == dst { action.as_ref() } else { None })
    })
}

fn render_full_mode<W: Write>(
    states: &IndexSet<State>,
    parents: &[Option<usize>],
    vars: &[Arc<str>],
    error_state: Option<usize>,
    all_edges: &[EdgeList],
    trace_path: &[usize],
    out: &mut W,
) -> std::io::Result<()> {
    let (trace_nodes, trace_edges) = build_trace_sets(trace_path);

    write_header(out)?;

    for (idx, state) in states.iter().enumerate() {
        let label = format_state_label(state, vars);
        let style = node_style(idx, error_state, &trace_nodes);
        write_node(out, idx, &label, style)?;
    }

    if all_edges.is_empty() {
        for (idx, parent) in parents.iter().enumerate() {
            if let Some(p) = parent {
                if trace_edges.contains(&(*p, idx)) {
                    writeln!(out, "  s{} -> s{} [color=red, penwidth=2];", p, idx)?;
                } else {
                    writeln!(out, "  s{} -> s{};", p, idx)?;
                }
            }
        }
    } else {
        for (src, targets) in all_edges.iter().enumerate() {
            for (dst, action) in targets {
                let is_trace = trace_edges.contains(&(src, *dst));
                let mut attrs = Vec::new();
                if let Some(label) = action {
                    attrs.push(format!("label=\"{}\"", escape_edge_label(label)));
                }
                if is_trace {
                    attrs.push("color=red".to_string());
                    attrs.push("penwidth=2".to_string());
                }
                if attrs.is_empty() {
                    writeln!(out, "  s{} -> s{};", src, dst)?;
                } else {
                    writeln!(out, "  s{} -> s{} [{}];", src, dst, attrs.join(", "))?;
                }
            }
        }
    }

    writeln!(out, "}}")
}

fn render_trace_mode<W: Write>(
    states: &IndexSet<State>,
    vars: &[Arc<str>],
    error_state: Option<usize>,
    all_edges: &[EdgeList],
    trace_path: &[usize],
    out: &mut W,
) -> std::io::Result<()> {
    let trace_nodes: HashSet<usize> = trace_path.iter().copied().collect();

    write_header(out)?;

    for &idx in trace_path {
        if let Some(state) = states.get_index(idx) {
            let label = format_state_label(state, vars);
            let style = node_style(idx, error_state, &trace_nodes);
            write_node(out, idx, &label, style)?;
        }
    }

    for w in trace_path.windows(2) {
        let (src, dst) = (w[0], w[1]);
        let mut attrs = vec!["color=red".to_string(), "penwidth=2".to_string()];
        if let Some(label) = find_edge_label(all_edges, src, dst) {
            attrs.insert(0, format!("label=\"{}\"", escape_edge_label(label)));
        }
        writeln!(out, "  s{} -> s{} [{}];", src, dst, attrs.join(", "))?;
    }

    writeln!(out, "}}")
}

fn render_clean_mode<W: Write>(
    states: &IndexSet<State>,
    parents: &[Option<usize>],
    vars: &[Arc<str>],
    error_state: Option<usize>,
    all_edges: &[EdgeList],
    trace_path: &[usize],
    out: &mut W,
) -> std::io::Result<()> {
    let (trace_nodes, trace_edges) = build_trace_sets(trace_path);

    write_header(out)?;

    for (idx, state) in states.iter().enumerate() {
        let label = format_state_label(state, vars);
        let style = node_style(idx, error_state, &trace_nodes);
        write_node(out, idx, &label, style)?;
    }

    if all_edges.is_empty() {
        for (idx, parent) in parents.iter().enumerate() {
            if let Some(p) = parent {
                if *p == idx {
                    continue;
                }
                if trace_edges.contains(&(*p, idx)) {
                    writeln!(out, "  s{} -> s{} [color=red, penwidth=2];", p, idx)?;
                } else {
                    writeln!(out, "  s{} -> s{};", p, idx)?;
                }
            }
        }
    } else {
        let mut merged: BTreeMap<(usize, usize), Vec<String>> = BTreeMap::new();
        for (src, targets) in all_edges.iter().enumerate() {
            for (dst, action) in targets {
                if src == *dst {
                    continue;
                }
                let key = (src, *dst);
                let label = action.as_ref().map(escape_edge_label).unwrap_or_default();
                merged.entry(key).or_default().push(label);
            }
        }

        for ((src, dst), labels) in &merged {
            let is_trace = trace_edges.contains(&(*src, *dst));
            let mut attrs = Vec::new();
            let combined: Vec<&str> = labels
                .iter()
                .filter(|l| !l.is_empty())
                .map(|l| l.as_str())
                .collect();
            if !combined.is_empty() {
                attrs.push(format!("label=\"{}\"", combined.join(", ")));
            }
            if is_trace {
                attrs.push("color=red".to_string());
                attrs.push("penwidth=2".to_string());
            }
            if attrs.is_empty() {
                writeln!(out, "  s{} -> s{};", src, dst)?;
            } else {
                writeln!(out, "  s{} -> s{} [{}];", src, dst, attrs.join(", "))?;
            }
        }
    }

    writeln!(out, "}}")
}

fn render_choices_mode<W: Write>(
    states: &IndexSet<State>,
    vars: &[Arc<str>],
    error_state: Option<usize>,
    all_edges: &[EdgeList],
    trace_path: &[usize],
    out: &mut W,
) -> std::io::Result<()> {
    let (trace_nodes, trace_edges) = build_trace_sets(trace_path);

    let mut visible_nodes: BTreeSet<usize> = trace_nodes.iter().copied().collect();
    for &node in trace_path {
        if let Some(edges) = all_edges.get(node) {
            for (dst, _) in edges {
                if *dst != node {
                    visible_nodes.insert(*dst);
                }
            }
        }
    }

    write_header(out)?;

    for &idx in &visible_nodes {
        if let Some(state) = states.get_index(idx) {
            let label = format_state_label(state, vars);
            if trace_nodes.contains(&idx) {
                let style = node_style(idx, error_state, &trace_nodes);
                write_node(out, idx, &label, style)?;
            } else {
                writeln!(out, "  s{} [label=\"{}\", style=dashed];", idx, label)?;
            }
        }
    }

    for &node in trace_path {
        if let Some(edges) = all_edges.get(node) {
            for (dst, action) in edges {
                if *dst == node {
                    continue;
                }
                if !visible_nodes.contains(dst) {
                    continue;
                }
                let is_trace = trace_edges.contains(&(node, *dst));
                let mut attrs = Vec::new();
                if let Some(label) = action {
                    attrs.push(format!("label=\"{}\"", escape_edge_label(label)));
                }
                if is_trace {
                    attrs.push("color=red".to_string());
                    attrs.push("penwidth=2".to_string());
                } else {
                    attrs.push("color=gray".to_string());
                    attrs.push("style=dashed".to_string());
                }
                writeln!(out, "  s{} -> s{} [{}];", node, dst, attrs.join(", "))?;
            }
        }
    }

    writeln!(out, "}}")
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dot_mode_from_str_valid() {
        assert_eq!("full".parse::<DotMode>().unwrap(), DotMode::Full);
        assert_eq!("trace".parse::<DotMode>().unwrap(), DotMode::Trace);
        assert_eq!("clean".parse::<DotMode>().unwrap(), DotMode::Clean);
        assert_eq!("choices".parse::<DotMode>().unwrap(), DotMode::Choices);
        assert_eq!("FULL".parse::<DotMode>().unwrap(), DotMode::Full);
        assert_eq!("Clean".parse::<DotMode>().unwrap(), DotMode::Clean);
    }

    #[test]
    fn dot_mode_from_str_invalid() {
        assert!("bogus".parse::<DotMode>().is_err());
        let err = "bogus".parse::<DotMode>().unwrap_err();
        assert!(err.contains("bogus"));
    }

    #[test]
    fn dot_mode_default_is_clean() {
        assert_eq!(DotMode::default(), DotMode::Clean);
    }

    #[test]
    fn dot_mode_display() {
        assert_eq!(DotMode::Full.to_string(), "full");
        assert_eq!(DotMode::Trace.to_string(), "trace");
        assert_eq!(DotMode::Clean.to_string(), "clean");
        assert_eq!(DotMode::Choices.to_string(), "choices");
    }

    fn make_state(values: Vec<Value>) -> State {
        State { values }
    }

    fn make_states_and_edges() -> (
        IndexSet<State>,
        Vec<Option<usize>>,
        Vec<Arc<str>>,
        Vec<EdgeList>,
    ) {
        let mut states = IndexSet::new();
        states.insert(make_state(vec![Value::Int(0)]));
        states.insert(make_state(vec![Value::Int(1)]));
        states.insert(make_state(vec![Value::Int(2)]));

        let parents = vec![None, Some(0), Some(1)];
        let vars = vec![Arc::from("x")];

        let all_edges = vec![
            vec![(1, Some(Arc::from("inc"))), (0, Some(Arc::from("self")))],
            vec![(2, Some(Arc::from("inc")))],
            vec![(0, Some(Arc::from("wrap")))],
        ];

        (states, parents, vars, all_edges)
    }

    #[test]
    fn render_trace_mode_only_trace_nodes() {
        let (states, _, vars, all_edges) = make_states_and_edges();
        let trace_path = vec![0, 1];

        let mut buf = Vec::new();
        render_trace_mode(&states, &vars, None, &all_edges, &trace_path, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(output.contains("s0"));
        assert!(output.contains("s1"));
        assert!(!output.contains("s2 ["), "s2 should not appear as a node");
        assert!(output.contains("s0 -> s1"));
        assert!(!output.contains("s1 -> s2"));
    }

    #[test]
    fn render_trace_fallback_to_full() {
        let (states, parents, vars, all_edges) = make_states_and_edges();
        let trace_path: Vec<usize> = vec![];

        let ctx = DotExport {
            states: &states,
            parents: &parents,
            vars: &vars,
            error_state: None,
            all_edges: &all_edges,
            trace_path: &trace_path,
            mode: DotMode::Trace,
        };
        let mut buf = Vec::new();
        export_dot(&ctx, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(output.contains("s0"));
        assert!(output.contains("s1"));
        assert!(output.contains("s2"));
    }

    #[test]
    fn render_clean_mode_omits_self_loops() {
        let (states, parents, vars, all_edges) = make_states_and_edges();
        let trace_path: Vec<usize> = vec![];

        let mut buf = Vec::new();
        render_clean_mode(
            &states,
            &parents,
            &vars,
            None,
            &all_edges,
            &trace_path,
            &mut buf,
        )
        .unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(!output.contains("s0 -> s0"), "self-loop should be omitted");
        assert!(output.contains("s0 -> s1"));
        assert!(output.contains("s1 -> s2"));
        assert!(output.contains("s2 -> s0"));
    }

    #[test]
    fn render_clean_mode_merges_parallel_edges() {
        let mut states = IndexSet::new();
        states.insert(make_state(vec![Value::Int(0)]));
        states.insert(make_state(vec![Value::Int(1)]));

        let parents = vec![None, Some(0)];
        let vars = vec![Arc::from("x")];
        let all_edges = vec![
            vec![
                (1, Some(Arc::from("actionA"))),
                (1, Some(Arc::from("actionB"))),
            ],
            vec![],
        ];

        let mut buf = Vec::new();
        render_clean_mode(&states, &parents, &vars, None, &all_edges, &[], &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        let edge_count = output.matches("s0 -> s1").count();
        assert_eq!(edge_count, 1, "parallel edges should be merged into one");
        assert!(output.contains("actionA"));
        assert!(output.contains("actionB"));
    }

    #[test]
    fn render_choices_mode_includes_alternatives() {
        let (states, _, vars, all_edges) = make_states_and_edges();
        let trace_path = vec![0, 1, 2];

        let mut buf = Vec::new();
        render_choices_mode(&states, &vars, Some(2), &all_edges, &trace_path, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(output.contains("s0"));
        assert!(output.contains("s1"));
        assert!(output.contains("s2"));
        assert!(output.contains("color=red"));
    }

    #[test]
    fn render_choices_fallback_to_full() {
        let (states, parents, vars, all_edges) = make_states_and_edges();
        let trace_path: Vec<usize> = vec![];

        let ctx = DotExport {
            states: &states,
            parents: &parents,
            vars: &vars,
            error_state: None,
            all_edges: &all_edges,
            trace_path: &trace_path,
            mode: DotMode::Choices,
        };
        let mut buf = Vec::new();
        export_dot(&ctx, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(output.contains("s0"));
        assert!(output.contains("s1"));
        assert!(output.contains("s2"));
    }
}
