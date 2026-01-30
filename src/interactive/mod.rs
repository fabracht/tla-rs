mod input;
mod render;
mod repl;
mod serialize;
mod state;

use std::fs;
use std::io;
use std::path::Path;
use std::sync::Arc;

use crossterm::{
    event::{DisableMouseCapture, EnableMouseCapture},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{backend::CrosstermBackend, Terminal};

use crate::ast::{Env, Spec, TransitionWithGuards};
use crate::eval::{init_states, make_primed_names, next_states, next_states_with_guards, Definitions};
use crate::stdlib;

use self::input::{run_app, run_replay_app};
use self::serialize::json_to_state;
use self::state::ExplorerState;

pub fn run_interactive(spec: &Spec, domains: &Env) -> io::Result<()> {
    let mut env = domains.clone();
    stdlib::load_builtins(&mut env);
    for module in &spec.extends {
        stdlib::load_module(module, &mut env);
    }

    let defs: Definitions = spec.definitions.clone();

    let initial_states = match init_states(&spec.init, &spec.vars, &env, &defs) {
        Ok(states) => states,
        Err(e) => {
            eprintln!("Error computing initial states: {:?}", e);
            return Ok(());
        }
    };

    if initial_states.is_empty() {
        eprintln!("No initial states found");
        return Ok(());
    }

    let initial = initial_states.into_iter().next().unwrap();

    let primed_vars = make_primed_names(&spec.vars);
    let initial_actions = match next_states(&spec.next, &initial, &spec.vars, &primed_vars, &mut env, &defs) {
        Ok(actions) => actions,
        Err(e) => {
            eprintln!("Error computing next states: {:?}", e);
            return Ok(());
        }
    };

    let initial_actions_with_guards = match next_states_with_guards(&spec.next, &initial, &spec.vars, &primed_vars, &mut env, &defs) {
        Ok(guards) => guards,
        Err(_) => initial_actions.iter().map(|t| TransitionWithGuards {
            transition: t.clone(),
            guards: Vec::new(),
            parameter_bindings: Vec::new(),
        }).collect(),
    };

    let mut explorer = ExplorerState::new(initial.clone(), initial_actions.clone(), initial_actions_with_guards.clone());

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let result = run_app(&mut terminal, &mut explorer, spec, &mut env, &defs, &initial, &initial_actions, &initial_actions_with_guards);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    result
}

pub fn run_interactive_replay(spec: &Spec, domains: &Env, replay_file: &Path) -> io::Result<()> {
    let content = fs::read_to_string(replay_file)?;
    let json: serde_json::Value = serde_json::from_str(&content)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("invalid JSON: {}", e)))?;

    let vars = &spec.vars;
    let trace_arr = json
        .get("trace")
        .and_then(|t| t.as_array())
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing trace array"))?;

    if trace_arr.is_empty() {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "empty trace"));
    }

    let invariant_name = json
        .get("invariant")
        .and_then(|i| i.as_str())
        .unwrap_or("(unknown)");
    let violated_idx = json
        .get("violated_invariant_index")
        .and_then(|i| i.as_u64())
        .map(|i| i as usize);

    let mut replay_trace: Vec<(crate::ast::State, Option<Arc<str>>)> = Vec::new();
    for entry in trace_arr {
        let action = entry
            .get("action")
            .and_then(|a| a.as_str())
            .map(Arc::from);
        let state = entry
            .get("state")
            .and_then(|s| json_to_state(s, vars))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "invalid state in trace"))?;
        replay_trace.push((state, action));
    }

    if replay_trace.is_empty() {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "no states in trace"));
    }

    let mut env = domains.clone();
    stdlib::load_builtins(&mut env);
    for module in &spec.extends {
        stdlib::load_module(module, &mut env);
    }

    let defs: Definitions = spec.definitions.clone();

    let (initial, _) = replay_trace.first().unwrap().clone();
    let primed_vars = make_primed_names(&spec.vars);
    let initial_actions = match next_states(&spec.next, &initial, &spec.vars, &primed_vars, &mut env, &defs) {
        Ok(actions) => actions,
        Err(e) => {
            eprintln!("Error computing next states: {:?}", e);
            return Ok(());
        }
    };

    let initial_actions_with_guards = match next_states_with_guards(&spec.next, &initial, &spec.vars, &primed_vars, &mut env, &defs) {
        Ok(guards) => guards,
        Err(_) => initial_actions.iter().map(|t| TransitionWithGuards {
            transition: t.clone(),
            guards: Vec::new(),
            parameter_bindings: Vec::new(),
        }).collect(),
    };

    let mut explorer = ExplorerState::new(initial.clone(), initial_actions.clone(), initial_actions_with_guards.clone());
    explorer.replay_mode = true;
    explorer.replay_trace = replay_trace;
    explorer.replay_position = 0;
    explorer.status_message = Some((
        format!("Replay mode: {} violation at step {} | [n]ext [p]rev [q]uit", invariant_name, violated_idx.unwrap_or(0)),
        false,
    ));

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let result = run_replay_app(&mut terminal, &mut explorer, spec, &mut env, &defs);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    result
}
