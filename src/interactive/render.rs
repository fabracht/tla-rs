use std::sync::Arc;

use ratatui::{
    Frame,
    layout::{Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, ListState, Paragraph, Wrap},
};

use crate::ast::{Env, Spec, State, Value};
use crate::checker::format_value;
use crate::eval::{Definitions, eval, explain_invariant_failure, state_to_env};

use super::state::{ExplorerState, InputMode};

pub(super) fn ui(
    f: &mut Frame,
    explorer: &ExplorerState,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
) {
    let objective_height = if spec.invariants.is_empty() {
        0
    } else {
        3 + spec.invariants.len().min(4) as u16
    };
    let tool_active = explorer.input_mode != InputMode::Normal;

    let main_chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(objective_height),
            Constraint::Min(10),
            Constraint::Length(12),
            Constraint::Length(4),
            Constraint::Length(1),
        ])
        .split(f.area());

    render_objectives(f, main_chunks[0], &explorer.current, spec, env, defs);

    if tool_active {
        let state_tool_split = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
            .split(main_chunks[1]);
        render_state(f, state_tool_split[0], &explorer.current, &spec.vars);
        render_tool_panel(f, state_tool_split[1], explorer);
    } else {
        render_state(f, main_chunks[1], &explorer.current, &spec.vars);
    }

    render_actions(f, main_chunks[2], explorer, &spec.vars);
    render_trace(f, main_chunks[3], explorer);
    render_status(f, main_chunks[4], explorer);
}

pub(super) fn ui_replay(
    f: &mut Frame,
    explorer: &ExplorerState,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
) {
    let objective_height = if spec.invariants.is_empty() {
        0
    } else {
        3 + spec.invariants.len().min(4) as u16
    };

    let main_chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(objective_height),
            Constraint::Min(6),
            Constraint::Length(4),
            Constraint::Length(4),
            Constraint::Length(1),
        ])
        .split(f.area());

    render_objectives(f, main_chunks[0], &explorer.current, spec, env, defs);
    render_state(f, main_chunks[1], &explorer.current, &spec.vars);
    render_replay_trace(f, main_chunks[2], explorer);
    render_repl(f, main_chunks[3], explorer);
    render_replay_status(f, main_chunks[4], explorer);
}

fn render_objectives(
    f: &mut Frame,
    area: Rect,
    state: &State,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
) {
    if spec.invariants.is_empty() {
        return;
    }

    let mut eval_env = env.clone();
    for (k, v) in state_to_env(state, &spec.vars) {
        eval_env.insert(k, v);
    }

    let mut lines: Vec<Line> = Vec::new();

    for (i, invariant) in spec.invariants.iter().enumerate() {
        let name = spec
            .invariant_names
            .get(i)
            .and_then(|n| n.as_ref())
            .map(|n| n.as_ref())
            .unwrap_or("(unnamed)");

        let (status, style, explanation) = match eval(invariant, &mut eval_env.clone(), defs) {
            Ok(Value::Bool(true)) => ("✓", Style::default().fg(Color::Green), None),
            Ok(Value::Bool(false)) => {
                let expl = explain_invariant_failure(invariant, state, spec, env, defs, name);
                (
                    "✗ VIOLATED",
                    Style::default().fg(Color::Red).add_modifier(Modifier::BOLD),
                    expl,
                )
            }
            _ => ("?", Style::default().fg(Color::Yellow), None),
        };

        lines.push(Line::from(vec![
            Span::styled(format!("  {} ", status), style),
            Span::styled(name.to_string(), style),
        ]));

        if let Some(expl) = explanation {
            if !expl.failing_bindings.is_empty() {
                let bindings_str: Vec<String> = expl
                    .failing_bindings
                    .iter()
                    .map(|(var, val)| format!("{}={}", var, format_value(val)))
                    .collect();
                lines.push(Line::from(vec![
                    Span::styled(
                        "     For ".to_string(),
                        Style::default().fg(Color::DarkGray),
                    ),
                    Span::styled(bindings_str.join(", "), Style::default().fg(Color::Yellow)),
                    Span::styled(":".to_string(), Style::default().fg(Color::DarkGray)),
                ]));
            }
            for sub_eval in expl.subexpression_evals.iter().take(3) {
                let check = if sub_eval.passed { "✓" } else { "✗" };
                let sub_style = if sub_eval.passed {
                    Style::default().fg(Color::Green)
                } else {
                    Style::default().fg(Color::Red)
                };
                lines.push(Line::from(vec![
                    Span::styled(format!("       {} ", check), sub_style),
                    Span::styled(sub_eval.expression.clone(), sub_style),
                    Span::styled(
                        format!(" = {}", format_value(&sub_eval.value)),
                        Style::default().fg(Color::DarkGray),
                    ),
                ]));
            }
        }
    }

    let widget = Paragraph::new(lines).block(
        Block::default()
            .borders(Borders::ALL)
            .title(" Objectives (Invariants) "),
    );

    f.render_widget(widget, area);
}

fn render_state(f: &mut Frame, area: Rect, state: &State, vars: &[Arc<str>]) {
    let mut lines: Vec<Line> = Vec::new();

    for (i, var) in vars.iter().enumerate() {
        if let Some(val) = state.values.get(i) {
            lines.push(Line::from(vec![
                Span::styled(format!("  {:12} = ", var), Style::default().fg(Color::Cyan)),
                Span::raw(format_value(val)),
            ]));
        }
    }

    let state_widget = Paragraph::new(lines)
        .block(Block::default().borders(Borders::ALL).title(" State "))
        .wrap(Wrap { trim: false });

    f.render_widget(state_widget, area);
}

fn format_nested_changes(
    old_val: &Value,
    new_val: &Value,
    path: &str,
) -> Vec<(String, String, String)> {
    let mut changes = Vec::new();
    match (old_val, new_val) {
        (Value::Fn(old_map), Value::Fn(new_map)) => {
            for (k, new_v) in new_map {
                let key_str = format_value(k);
                let new_path = format!("{}[{}]", path, key_str);
                match old_map.get(k) {
                    Some(old_v) if old_v != new_v => {
                        changes.extend(format_nested_changes(old_v, new_v, &new_path));
                    }
                    None => {
                        changes.push((new_path, String::new(), format_value(new_v)));
                    }
                    _ => {}
                }
            }
            for k in old_map.keys() {
                if !new_map.contains_key(k) {
                    let key_str = format_value(k);
                    let new_path = format!("{}[{}]", path, key_str);
                    changes.push((
                        new_path,
                        format_value(old_map.get(k).unwrap()),
                        String::new(),
                    ));
                }
            }
        }
        (Value::Record(old_rec), Value::Record(new_rec)) => {
            for (k, new_v) in new_rec {
                let new_path = format!("{}.{}", path, k);
                match old_rec.get(k) {
                    Some(old_v) if old_v != new_v => {
                        changes.extend(format_nested_changes(old_v, new_v, &new_path));
                    }
                    None => {
                        changes.push((new_path, String::new(), format_value(new_v)));
                    }
                    _ => {}
                }
            }
        }
        _ => {
            changes.push((
                path.to_string(),
                format_value(old_val),
                format_value(new_val),
            ));
        }
    }
    changes
}

fn render_actions(f: &mut Frame, area: Rect, explorer: &ExplorerState, vars: &[Arc<str>]) {
    let guard_indicator = if explorer.show_guards {
        " [g:ON] "
    } else {
        " [g:off] "
    };
    let title = format!(" Available Actions{}", guard_indicator);

    let mut items: Vec<ListItem> = Vec::new();

    if explorer.available_actions.is_empty() {
        items.push(
            ListItem::new("  DEADLOCK — no actions available from this state")
                .style(Style::default().fg(Color::Red).add_modifier(Modifier::BOLD)),
        );
        items.push(
            ListItem::new("  Press [b] to backtrack or [r] to reset")
                .style(Style::default().fg(Color::DarkGray)),
        );
    }

    for (i, transition) in explorer.available_actions.iter().enumerate() {
        let action_name = transition
            .action
            .as_ref()
            .map(|s| s.as_ref())
            .unwrap_or("(unnamed)");

        let mut all_changes: Vec<(String, String, String)> = Vec::new();
        for (vi, var) in vars.iter().enumerate() {
            if let (Some(old_val), Some(new_val)) = (
                explorer.current.values.get(vi),
                transition.state.values.get(vi),
            ) && old_val != new_val
            {
                all_changes.extend(format_nested_changes(old_val, new_val, var));
            }
        }

        let is_expanded = i == explorer.selected_action || explorer.expanded_actions.contains(&i);
        let is_grouped = all_changes.len() > 3;

        let change_str = if all_changes.is_empty() {
            "(no changes)".to_string()
        } else if !is_grouped {
            all_changes
                .iter()
                .map(|(path, old, new)| {
                    if old.is_empty() {
                        format!("{}': {}", path, new)
                    } else if new.is_empty() {
                        format!("{}': (removed)", path)
                    } else {
                        format!("{}': {} -> {}", path, old, new)
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        } else if is_expanded {
            format!("▾ {} changes", all_changes.len())
        } else {
            format!("▸ {} changes", all_changes.len())
        };

        let style = if i == explorer.selected_action {
            Style::default()
                .fg(Color::Yellow)
                .add_modifier(Modifier::BOLD)
        } else {
            Style::default()
        };

        let prefix = if i == explorer.selected_action {
            "▸ "
        } else {
            "  "
        };
        items.push(
            ListItem::new(format!(
                "{}[{}] {}: {}",
                prefix,
                i + 1,
                action_name,
                change_str
            ))
            .style(style),
        );

        if is_grouped && is_expanded {
            for (path, old, new) in &all_changes {
                let detail = if old.is_empty() {
                    format!("       {}': {}", path, new)
                } else if new.is_empty() {
                    format!("       {}': (removed)", path)
                } else {
                    format!("       {}': {} -> {}", path, old, new)
                };
                items.push(ListItem::new(detail).style(Style::default().fg(Color::DarkGray)));
            }
        }

        if explorer.show_guards
            && let Some(transition_with_guards) = explorer.available_actions_with_guards.get(i)
        {
            if transition_with_guards.guards.is_empty() {
                items.push(
                    ListItem::new("       (no preconditions)")
                        .style(Style::default().fg(Color::DarkGray)),
                );
            } else {
                for guard in &transition_with_guards.guards {
                    let check = if guard.result { "✓" } else { "✗" };
                    let guard_style = if guard.result {
                        Style::default().fg(Color::Green)
                    } else {
                        Style::default().fg(Color::Red)
                    };
                    items.push(
                        ListItem::new(format!("       {} {}", check, guard.expression))
                            .style(guard_style),
                    );
                }
            }
        }
    }

    let actions_widget =
        List::new(items).block(Block::default().borders(Borders::ALL).title(title));

    let mut list_state = ListState::default();
    list_state.select(Some(explorer.selected_action));

    f.render_stateful_widget(actions_widget, area, &mut list_state);
}

fn render_trace(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let trace_items: Vec<String> = std::iter::once("Init".to_string())
        .chain(explorer.history.iter().map(|(_, action)| {
            action
                .as_ref()
                .map(|s| s.to_string())
                .unwrap_or_else(|| "(unnamed)".to_string())
        }))
        .collect();

    let trace_text = trace_items.join(" → ") + " → [current]";

    let trace_widget = Paragraph::new(trace_text)
        .block(Block::default().borders(Borders::ALL).title(" Trace "))
        .wrap(Wrap { trim: false });

    f.render_widget(trace_widget, area);
}

pub(super) fn render_repl(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let (title, input, output, placeholder) = match explorer.input_mode {
        InputMode::Repl => (
            " REPL (Esc to exit) ",
            &explorer.repl_input,
            explorer.repl_output.as_deref(),
            "Type expression and press Enter",
        ),
        InputMode::Trace => (
            " Variable Trace (Esc to exit) ",
            &explorer.trace_input,
            None,
            "Enter variable path (e.g., client_seq[a][d1]) or leave empty for all",
        ),
        InputMode::Hypothesis => (
            " Hypothesis Test (Esc to exit) ",
            &explorer.hypothesis_input,
            explorer.hypothesis_output.as_deref(),
            "Enter guard expression (e.g., seq > client_seq[c][d])",
        ),
        InputMode::Walk => (
            " Random Walk (Esc to exit) ",
            &explorer.walk_input,
            None,
            "Enter number of steps (e.g., 50)",
        ),
        InputMode::StepUntil => (
            " Step Until (Esc to exit) ",
            &explorer.step_until_input,
            None,
            "Enter condition [;max_steps] (e.g., x > 3;500)",
        ),
        InputMode::Normal => (
            " REPL ",
            &explorer.repl_input,
            explorer.repl_output.as_deref(),
            "",
        ),
    };

    let mut lines: Vec<Line> = Vec::new();

    match explorer.input_mode {
        InputMode::Normal => {
            lines.push(Line::from(Span::styled(
                "Press 'e'=eval 't'=trace 'w'=walk 'u'=until 'h'=hypothesis",
                Style::default().fg(Color::DarkGray),
            )));
            if let Some(ref output_text) = explorer.repl_output {
                lines.push(Line::from(Span::styled(
                    output_text,
                    Style::default().fg(Color::Yellow),
                )));
            }
        }
        InputMode::Repl
        | InputMode::Trace
        | InputMode::Hypothesis
        | InputMode::Walk
        | InputMode::StepUntil => {
            lines.push(Line::from(vec![
                Span::styled("> ", Style::default().fg(Color::Green)),
                Span::raw(input),
                Span::styled("█", Style::default().fg(Color::White)),
            ]));
            if input.is_empty() {
                lines.push(Line::from(Span::styled(
                    placeholder,
                    Style::default().fg(Color::DarkGray),
                )));
            }
            if let Some(output_text) = output {
                for line in output_text.lines() {
                    lines.push(Line::from(Span::styled(
                        line,
                        Style::default().fg(Color::Yellow),
                    )));
                }
            }
        }
    }

    if explorer.input_mode == InputMode::Trace
        && let Some(ref trace_results) = explorer.trace_output
    {
        if trace_results.is_empty() {
            lines.push(Line::from(Span::styled(
                "  No changes found",
                Style::default().fg(Color::DarkGray),
            )));
        } else {
            for change in trace_results.iter().take(10) {
                let action_str = change
                    .action
                    .as_ref()
                    .map(|a| a.to_string())
                    .unwrap_or_else(|| "Init".to_string());
                lines.push(Line::from(vec![
                    Span::styled(
                        format!("  [{}] ", change.state_idx),
                        Style::default().fg(Color::Cyan),
                    ),
                    Span::styled(&change.path, Style::default().fg(Color::White)),
                    Span::raw(": "),
                    Span::styled(
                        format_value(&change.old_value),
                        Style::default().fg(Color::Red),
                    ),
                    Span::raw(" -> "),
                    Span::styled(
                        format_value(&change.new_value),
                        Style::default().fg(Color::Green),
                    ),
                    Span::styled(
                        format!(" ({})", action_str),
                        Style::default().fg(Color::DarkGray),
                    ),
                ]));
            }
            if trace_results.len() > 10 {
                lines.push(Line::from(Span::styled(
                    format!("  ... and {} more", trace_results.len() - 10),
                    Style::default().fg(Color::DarkGray),
                )));
            }
        }
    }

    let repl_widget =
        Paragraph::new(lines).block(Block::default().borders(Borders::ALL).title(title));

    f.render_widget(repl_widget, area);
}

fn render_tool_panel(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let (title, input, placeholder) = match explorer.input_mode {
        InputMode::Repl => (
            " REPL (Enter=eval, Esc=exit) ",
            &explorer.repl_input,
            "Type TLA+ expression...",
        ),
        InputMode::Trace => (
            " Variable Trace (Enter=exit, Esc=exit) ",
            &explorer.trace_input,
            "Type to filter (e.g., small, big)...",
        ),
        InputMode::Hypothesis => (
            " Hypothesis Test (Enter=test, Esc=exit) ",
            &explorer.hypothesis_input,
            "Enter guard expression...",
        ),
        InputMode::Walk => (
            " Random Walk (Enter=go, Esc=exit) ",
            &explorer.walk_input,
            "Enter number of steps (e.g., 50)...",
        ),
        InputMode::StepUntil => (
            " Step Until (Enter=go, Esc=exit) ",
            &explorer.step_until_input,
            "Enter condition [;max_steps]...",
        ),
        InputMode::Normal => (" Tools ", &explorer.repl_input, ""),
    };

    let mut lines: Vec<Line> = Vec::new();

    lines.push(Line::from(vec![
        Span::styled("> ", Style::default().fg(Color::Green)),
        Span::raw(input.as_str()),
        Span::styled("█", Style::default().fg(Color::White)),
    ]));

    if input.is_empty() {
        lines.push(Line::from(Span::styled(
            placeholder,
            Style::default().fg(Color::DarkGray),
        )));
    }

    lines.push(Line::from(""));

    match explorer.input_mode {
        InputMode::Trace => {
            if let Some(ref trace_results) = explorer.trace_output {
                if trace_results.is_empty() {
                    lines.push(Line::from(Span::styled(
                        "No changes found",
                        Style::default().fg(Color::DarkGray),
                    )));
                } else {
                    for (i, change) in trace_results.iter().enumerate() {
                        let action_str = change
                            .action
                            .as_ref()
                            .map(|a| a.to_string())
                            .unwrap_or_else(|| "Init".to_string());
                        let connector = if i == trace_results.len() - 1 {
                            "└"
                        } else {
                            "├"
                        };
                        lines.push(Line::from(vec![
                            Span::styled(
                                format!(" {} ", connector),
                                Style::default().fg(Color::DarkGray),
                            ),
                            Span::styled(
                                format!("[{}]", change.state_idx),
                                Style::default().fg(Color::Cyan),
                            ),
                            Span::raw(" "),
                            Span::styled(&change.path, Style::default().fg(Color::White)),
                            Span::styled(" = ", Style::default().fg(Color::DarkGray)),
                            Span::styled(
                                format_value(&change.old_value),
                                Style::default().fg(Color::Red),
                            ),
                            Span::styled(" → ", Style::default().fg(Color::Yellow)),
                            Span::styled(
                                format_value(&change.new_value),
                                Style::default().fg(Color::Green),
                            ),
                            Span::styled(
                                format!("  {}", action_str),
                                Style::default().fg(Color::DarkGray),
                            ),
                        ]));
                    }
                }
            }
        }
        InputMode::Repl => {
            if let Some(ref output) = explorer.repl_output {
                for line in output.lines() {
                    lines.push(Line::from(Span::styled(
                        line,
                        Style::default().fg(Color::Yellow),
                    )));
                }
            }
        }
        InputMode::Hypothesis => {
            if let Some(ref output) = explorer.hypothesis_output {
                for line in output.lines() {
                    let style = if line.contains("BLOCKED") || line.contains("prevented") {
                        Style::default().fg(Color::Green)
                    } else if line.contains("would pass") {
                        Style::default().fg(Color::Yellow)
                    } else {
                        Style::default().fg(Color::White)
                    };
                    lines.push(Line::from(Span::styled(line, style)));
                }
            }
        }
        InputMode::Walk | InputMode::StepUntil | InputMode::Normal => {}
    }

    let widget = Paragraph::new(lines)
        .block(Block::default().borders(Borders::ALL).title(title))
        .wrap(Wrap { trim: false });

    f.render_widget(widget, area);
}

pub(super) fn render_replay_trace(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let total = explorer.replay_trace.len();
    let pos = explorer.replay_position;

    let mut trace_items: Vec<String> = Vec::new();
    for (i, (_, action)) in explorer.replay_trace.iter().enumerate() {
        let name = action
            .as_ref()
            .map(|a| a.to_string())
            .unwrap_or_else(|| "Init".to_string());
        let marker = if i == pos { ">" } else { " " };
        trace_items.push(format!("{}[{}] {}", marker, i, name));
    }

    let start = pos.saturating_sub(5);
    let end = (start + 10).min(total);
    let visible: Vec<_> = trace_items[start..end].to_vec();

    let trace_text = format!("Position: {}/{}\n{}", pos, total - 1, visible.join(" → "));

    let trace_widget = Paragraph::new(trace_text)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title(" Replay Trace "),
        )
        .wrap(Wrap { trim: false });

    f.render_widget(trace_widget, area);
}

fn render_replay_status(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let status = if let Some((ref msg, is_error)) = explorer.status_message {
        let color = if is_error { Color::Red } else { Color::Green };
        Line::from(Span::styled(msg, Style::default().fg(color)))
    } else {
        Line::from(vec![
            Span::styled("[n/→]", Style::default().fg(Color::Cyan)),
            Span::raw(" next "),
            Span::styled("[p/←]", Style::default().fg(Color::Cyan)),
            Span::raw(" prev "),
            Span::styled("[e]", Style::default().fg(Color::Cyan)),
            Span::raw(" eval "),
            Span::styled("[q]", Style::default().fg(Color::Cyan)),
            Span::raw(" quit"),
        ])
    };

    let status_widget = Paragraph::new(status);
    f.render_widget(status_widget, area);
}

fn render_status(f: &mut Frame, area: Rect, explorer: &ExplorerState) {
    let status = if let Some((ref msg, is_error)) = explorer.status_message {
        let color = if is_error { Color::Red } else { Color::Green };
        Line::from(Span::styled(msg, Style::default().fg(color)))
    } else {
        match explorer.input_mode {
            InputMode::Repl => Line::from(Span::styled(
                "Type expression and press Enter | Esc: exit",
                Style::default().fg(Color::DarkGray),
            )),
            InputMode::Trace => Line::from(Span::styled(
                "Enter variable path and press Enter | Esc: exit",
                Style::default().fg(Color::DarkGray),
            )),
            InputMode::Hypothesis => Line::from(Span::styled(
                "Enter guard expression (with primed vars) | Esc: exit",
                Style::default().fg(Color::DarkGray),
            )),
            InputMode::Walk => Line::from(Span::styled(
                "Enter number of random steps | Esc: exit",
                Style::default().fg(Color::DarkGray),
            )),
            InputMode::StepUntil => Line::from(Span::styled(
                "Enter condition [;max_steps] | Esc: exit",
                Style::default().fg(Color::DarkGray),
            )),
            InputMode::Normal => Line::from(vec![
                Span::styled("⏎", Style::default().fg(Color::Cyan)),
                Span::raw("act "),
                Span::styled("↑↓", Style::default().fg(Color::Cyan)),
                Span::raw("sel "),
                Span::styled("→", Style::default().fg(Color::Cyan)),
                Span::raw("xpand "),
                Span::styled("b", Style::default().fg(Color::Cyan)),
                Span::raw("ack "),
                Span::styled("r", Style::default().fg(Color::Cyan)),
                Span::raw("eset "),
                Span::styled("e", Style::default().fg(Color::Cyan)),
                Span::raw("val "),
                Span::styled("t", Style::default().fg(Color::Cyan)),
                Span::raw("race "),
                Span::styled("w", Style::default().fg(Color::Cyan)),
                Span::raw("alk "),
                Span::styled("u", Style::default().fg(Color::Cyan)),
                Span::raw("ntil "),
                Span::styled("g", Style::default().fg(Color::Cyan)),
                Span::raw("uards "),
                Span::styled("h", Style::default().fg(Color::Cyan)),
                Span::raw("ypo "),
                Span::styled("s", Style::default().fg(Color::Cyan)),
                Span::raw("ave/"),
                Span::styled("l", Style::default().fg(Color::Cyan)),
                Span::raw("oad "),
                Span::styled("q", Style::default().fg(Color::Cyan)),
                Span::raw("uit"),
            ]),
        }
    };

    let status_widget = Paragraph::new(status);
    f.render_widget(status_widget, area);
}
