use std::io;
use std::path::Path;

use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use ratatui::{Terminal, backend::CrosstermBackend};

use crate::ast::{Env, Spec, State, Transition, TransitionWithGuards};
use crate::eval::{Definitions, make_primed_names, next_states, next_states_with_guards};

use super::render::{ui, ui_replay};
use super::repl::{eval_repl, test_hypothesis};
use super::state::{ExplorerState, InputMode};

pub(super) fn enter_free_exploration(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    start: State,
    spec: &Spec,
    env: &mut Env,
    defs: &Definitions,
) -> io::Result<()> {
    let primed = make_primed_names(&spec.vars);
    let (initial_actions, guards) = match &spec.next {
        Some(next_expr) => {
            let actions =
                next_states(next_expr, &start, &spec.vars, &primed, env, defs).unwrap_or_default();
            let guards = next_states_with_guards(next_expr, &start, &spec.vars, &primed, env, defs)
                .unwrap_or_else(|_| {
                    actions
                        .iter()
                        .map(|t| TransitionWithGuards {
                            transition: t.clone(),
                            guards: Vec::new(),
                            parameter_bindings: Vec::new(),
                        })
                        .collect()
                });
            (actions, guards)
        }
        None => (Vec::new(), Vec::new()),
    };

    let mut free = ExplorerState::new(start.clone(), initial_actions.clone(), guards.clone());
    free.status_message = Some((
        "Free exploration — [Enter] take action, [b]acktrack, [e] repl, [q] back to demo".into(),
        false,
    ));
    let mut ctx = AppContext {
        spec,
        env,
        defs,
        initial: &start,
        initial_actions: &initial_actions,
        initial_actions_with_guards: &guards,
    };
    run_app(terminal, &mut free, &mut ctx)
}

pub(super) struct AppContext<'a> {
    pub spec: &'a Spec,
    pub env: &'a mut Env,
    pub defs: &'a Definitions,
    pub initial: &'a State,
    pub initial_actions: &'a [Transition],
    pub initial_actions_with_guards: &'a [TransitionWithGuards],
}

pub(super) fn run_app(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    explorer: &mut ExplorerState,
    ctx: &mut AppContext<'_>,
) -> io::Result<()> {
    loop {
        terminal.draw(|f| ui(f, explorer, ctx.spec, ctx.env, ctx.defs))?;

        if let Event::Key(key) = event::read()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }

            explorer.status_message = None;

            match explorer.input_mode {
                InputMode::Repl => match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.repl_input.clear();
                        explorer.repl_output = None;
                    }
                    KeyCode::Enter => {
                        let result = eval_repl(
                            &explorer.repl_input,
                            &explorer.current,
                            ctx.spec,
                            ctx.env,
                            ctx.defs,
                        );
                        explorer.repl_output = Some(result);
                        explorer.repl_input.clear();
                    }
                    KeyCode::Backspace => {
                        explorer.repl_input.pop();
                    }
                    KeyCode::Char(c) => {
                        explorer.repl_input.push(c);
                    }
                    _ => {}
                },
                InputMode::Trace => match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.trace_input.clear();
                        explorer.trace_output = None;
                    }
                    KeyCode::Enter => {
                        explorer.input_mode = InputMode::Normal;
                    }
                    KeyCode::Backspace => {
                        explorer.trace_input.pop();
                        explorer.trace_output = Some(explorer.compute_trace(&explorer.trace_input));
                    }
                    KeyCode::Char(c) => {
                        explorer.trace_input.push(c);
                        explorer.trace_output = Some(explorer.compute_trace(&explorer.trace_input));
                    }
                    _ => {}
                },
                InputMode::Hypothesis => match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.hypothesis_input.clear();
                        explorer.hypothesis_output = None;
                    }
                    KeyCode::Enter => {
                        let result = test_hypothesis(
                            &explorer.hypothesis_input,
                            &explorer.history,
                            &explorer.current,
                            ctx.spec,
                            ctx.env,
                            ctx.defs,
                        );
                        explorer.hypothesis_output = Some(result);
                        explorer.hypothesis_input.clear();
                    }
                    KeyCode::Backspace => {
                        explorer.hypothesis_input.pop();
                    }
                    KeyCode::Char(c) => {
                        explorer.hypothesis_input.push(c);
                    }
                    _ => {}
                },
                InputMode::Walk => match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.walk_input.clear();
                    }
                    KeyCode::Enter => {
                        explorer.input_mode = InputMode::Normal;
                        match explorer.walk_input.trim().parse::<usize>() {
                            Ok(0) => {
                                explorer.status_message = Some(("Steps must be > 0".into(), true));
                            }
                            Ok(n) => {
                                explorer.random_walk(n, ctx.spec, ctx.env, ctx.defs);
                            }
                            Err(_) => {
                                explorer.status_message = Some(("Invalid number".into(), true));
                            }
                        }
                        explorer.walk_input.clear();
                    }
                    KeyCode::Backspace => {
                        explorer.walk_input.pop();
                    }
                    KeyCode::Char(c) => {
                        explorer.walk_input.push(c);
                    }
                    _ => {}
                },
                InputMode::StepUntil => match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.step_until_input.clear();
                    }
                    KeyCode::Enter => {
                        explorer.input_mode = InputMode::Normal;
                        let input = explorer.step_until_input.clone();
                        explorer.step_until_input.clear();
                        let (expr_str, max_steps) = match input.rfind(';') {
                            Some(pos) => {
                                let after = input[pos + 1..].trim();
                                match after.parse::<usize>() {
                                    Ok(n) if n > 0 => (&input[..pos], n),
                                    _ => (input.as_str(), 1000),
                                }
                            }
                            None => (input.as_str(), 1000),
                        };
                        match crate::parser::parse_expr(expr_str) {
                            Ok(condition) => {
                                explorer
                                    .step_until(&condition, max_steps, ctx.spec, ctx.env, ctx.defs);
                            }
                            Err(e) => {
                                explorer.status_message =
                                    Some((format!("Parse error: {}", e.message), true));
                            }
                        }
                    }
                    KeyCode::Backspace => {
                        explorer.step_until_input.pop();
                    }
                    KeyCode::Char(c) => {
                        explorer.step_until_input.push(c);
                    }
                    _ => {}
                },
                InputMode::Normal => match key.code {
                    KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                    KeyCode::Down | KeyCode::Char('j') => explorer.select_next(),
                    KeyCode::Up | KeyCode::Char('k') => explorer.select_prev(),
                    KeyCode::Right | KeyCode::Char(' ') => explorer.toggle_expand(),
                    KeyCode::Left => explorer.collapse_selected(),
                    KeyCode::Enter => explorer.take_action(ctx.spec, ctx.env, ctx.defs),
                    KeyCode::Char('b') => explorer.backtrack(ctx.spec, ctx.env, ctx.defs),
                    KeyCode::Char('r') => {
                        explorer.reset(
                            ctx.initial.clone(),
                            ctx.initial_actions.to_vec(),
                            ctx.initial_actions_with_guards.to_vec(),
                        );
                    }
                    KeyCode::Char('e') => {
                        explorer.input_mode = InputMode::Repl;
                        explorer.repl_output = None;
                    }
                    KeyCode::Char('t') => {
                        explorer.input_mode = InputMode::Trace;
                        explorer.trace_input.clear();
                        explorer.trace_output = Some(explorer.compute_trace(""));
                    }
                    KeyCode::Char('g') => {
                        explorer.show_guards = !explorer.show_guards;
                        let status = if explorer.show_guards {
                            "Guards ON"
                        } else {
                            "Guards OFF"
                        };
                        explorer.status_message = Some((status.into(), false));
                    }
                    KeyCode::Char('h') => {
                        explorer.input_mode = InputMode::Hypothesis;
                        explorer.hypothesis_output = None;
                    }
                    KeyCode::Char('w') => {
                        explorer.input_mode = InputMode::Walk;
                        explorer.walk_input.clear();
                    }
                    KeyCode::Char('u') => {
                        explorer.input_mode = InputMode::StepUntil;
                        explorer.step_until_input.clear();
                    }
                    KeyCode::Char('s') => {
                        let path = Path::new("trace.json");
                        match explorer.save_trace(path, &ctx.spec.vars, ctx.initial) {
                            Ok(()) => {
                                explorer.status_message =
                                    Some((format!("Saved trace to {}", path.display()), false));
                            }
                            Err(e) => {
                                explorer.status_message =
                                    Some((format!("Save failed: {}", e), true));
                            }
                        }
                    }
                    KeyCode::Char('l') => {
                        let path = Path::new("trace.json");
                        match ExplorerState::load_trace(
                            path,
                            ctx.spec,
                            ctx.env,
                            ctx.defs,
                            ctx.initial,
                        ) {
                            Ok(loaded) => {
                                *explorer = loaded;
                                explorer.status_message =
                                    Some((format!("Loaded trace from {}", path.display()), false));
                            }
                            Err(e) => {
                                explorer.status_message =
                                    Some((format!("Load failed: {}", e), true));
                            }
                        }
                    }
                    _ => {}
                },
            }
        }
    }
}

pub(super) fn run_replay_app(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    explorer: &mut ExplorerState,
    spec: &Spec,
    env: &mut Env,
    defs: &Definitions,
) -> io::Result<()> {
    loop {
        terminal.draw(|f| ui_replay(f, explorer, spec, env, defs))?;

        if let Event::Key(key) = event::read()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }

            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                KeyCode::Char('n') | KeyCode::Right | KeyCode::Down => {
                    if explorer.replay_position < explorer.replay_trace.len() - 1 {
                        explorer.replay_position += 1;
                        explorer.current =
                            explorer.replay_trace[explorer.replay_position].0.clone();
                        let action = &explorer.replay_trace[explorer.replay_position].1;
                        explorer.status_message = Some((
                            format!(
                                "Step {}/{} - {}",
                                explorer.replay_position,
                                explorer.replay_trace.len() - 1,
                                action
                                    .as_ref()
                                    .map(|a| a.to_string())
                                    .unwrap_or_else(|| "Init".to_string())
                            ),
                            false,
                        ));
                    } else {
                        explorer.status_message = Some(("At end of trace".to_string(), true));
                    }
                }
                KeyCode::Char('p') | KeyCode::Left | KeyCode::Up => {
                    if explorer.replay_position > 0 {
                        explorer.replay_position -= 1;
                        explorer.current =
                            explorer.replay_trace[explorer.replay_position].0.clone();
                        let action = &explorer.replay_trace[explorer.replay_position].1;
                        explorer.status_message = Some((
                            format!(
                                "Step {}/{} - {}",
                                explorer.replay_position,
                                explorer.replay_trace.len() - 1,
                                action
                                    .as_ref()
                                    .map(|a| a.to_string())
                                    .unwrap_or_else(|| "Init".to_string())
                            ),
                            false,
                        ));
                    } else {
                        explorer.status_message = Some(("At start of trace".to_string(), true));
                    }
                }
                KeyCode::Char('e') => {
                    explorer.input_mode = InputMode::Repl;
                    explorer.repl_output = None;
                }
                KeyCode::Char('f') => {
                    enter_free_exploration(terminal, explorer.current.clone(), spec, env, defs)?;
                }
                _ => {}
            }

            if explorer.input_mode == InputMode::Repl {
                match key.code {
                    KeyCode::Esc => {
                        explorer.input_mode = InputMode::Normal;
                        explorer.repl_input.clear();
                        explorer.repl_output = None;
                    }
                    KeyCode::Enter => {
                        let result =
                            eval_repl(&explorer.repl_input, &explorer.current, spec, env, defs);
                        explorer.repl_output = Some(result);
                        explorer.repl_input.clear();
                    }
                    KeyCode::Backspace => {
                        explorer.repl_input.pop();
                    }
                    KeyCode::Char(c) if explorer.input_mode == InputMode::Repl => {
                        explorer.repl_input.push(c);
                    }
                    _ => {}
                }
            }
        }
    }
}
