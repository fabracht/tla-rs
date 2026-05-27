use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyEventKind},
    execute,
    terminal::{EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode},
};
use ratatui::{
    Frame, Terminal,
    backend::CrosstermBackend,
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, Paragraph, Wrap},
};

use crate::ast::{Env, Spec, State};
use crate::checker::prepare_spec;
use crate::demo::beat::parse_variant_constants;
use crate::demo::{Beat, Manifest, Variant};
use crate::eval::Definitions;
use crate::load::prepare_from_path;
use crate::scenario::{ScenarioStep, execute_scenario_with, parse_scenario};
use crate::trace_io::json_to_state;

use super::input::enter_free_exploration;
use super::render::ui_present;
use super::state::ExplorerState;

type Trace = Vec<(State, Option<Arc<str>>)>;

pub(super) struct PresentHeader {
    pub title: String,
    pub note: Option<String>,
    pub beat_index: usize,
    pub beat_total: usize,
    pub variant: String,
    pub variant_index: usize,
    pub variant_total: usize,
    pub step: usize,
    pub step_total: usize,
}

enum PresentNav {
    NextBeat,
    PrevBeat,
    NextVariant,
    Quit,
}

struct PreparedVariant {
    spec: Spec,
    env: Env,
    defs: Definitions,
    trace: Trace,
}

pub fn run_presentation(manifest_path: &Path) -> io::Result<()> {
    let manifest = match Manifest::load(manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: {}", e);
            return Ok(());
        }
    };
    if manifest.beats.is_empty() {
        eprintln!("manifest has no beats");
        return Ok(());
    }
    let dir = manifest_path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let result = present_loop(&mut terminal, &manifest, &dir);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;
    result
}

fn present_loop(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    manifest: &Manifest,
    dir: &Path,
) -> io::Result<()> {
    let beat_total = manifest.beats.len();
    let mut beat_index = 0usize;
    let mut variant_index = 0usize;

    loop {
        let beat = &manifest.beats[beat_index];
        let variant_names = beat.target_variants();
        let variant_total = variant_names.len().max(1);
        if variant_index >= variant_total {
            variant_index = 0;
        }
        let variant_name = variant_names
            .get(variant_index)
            .cloned()
            .unwrap_or_default();

        let prepared = manifest
            .variants
            .get(&variant_name)
            .ok_or_else(|| format!("unknown variant {:?}", variant_name))
            .and_then(|variant| prepare_variant(dir, beat, variant));

        let nav = match prepared {
            Ok(mut prepared) => play_beat(
                terminal,
                beat,
                beat_index,
                beat_total,
                &variant_name,
                variant_index,
                variant_total,
                &mut prepared,
            )?,
            Err(msg) => show_error(
                terminal,
                beat,
                beat_index,
                beat_total,
                &variant_name,
                variant_total,
                &msg,
            )?,
        };

        match nav {
            PresentNav::Quit => return Ok(()),
            PresentNav::NextBeat => {
                beat_index = (beat_index + 1) % beat_total;
                variant_index = 0;
            }
            PresentNav::PrevBeat => {
                beat_index = (beat_index + beat_total - 1) % beat_total;
                variant_index = 0;
            }
            PresentNav::NextVariant => {
                variant_index = (variant_index + 1) % variant_total;
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn play_beat(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    beat: &Beat,
    beat_index: usize,
    beat_total: usize,
    variant_name: &str,
    variant_index: usize,
    variant_total: usize,
    prepared: &mut PreparedVariant,
) -> io::Result<PresentNav> {
    let last = prepared.trace.len().saturating_sub(1);
    let mut explorer = ExplorerState::new(prepared.trace[0].0.clone(), Vec::new(), Vec::new());
    explorer.replay_mode = true;
    explorer.replay_trace = prepared.trace.clone();
    explorer.replay_position = 0;

    loop {
        let header = PresentHeader {
            title: beat.title.clone(),
            note: beat.note.clone(),
            beat_index,
            beat_total,
            variant: variant_name.to_string(),
            variant_index,
            variant_total,
            step: explorer.replay_position,
            step_total: last,
        };
        terminal.draw(|f| {
            ui_present(
                f,
                &explorer,
                &header,
                &prepared.spec,
                &prepared.env,
                &prepared.defs,
            )
        })?;

        if let Event::Key(key) = event::read()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }
            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(PresentNav::Quit),
                KeyCode::Right => return Ok(PresentNav::NextBeat),
                KeyCode::Left => return Ok(PresentNav::PrevBeat),
                KeyCode::Char('v') | KeyCode::Tab => return Ok(PresentNav::NextVariant),
                KeyCode::Char('n') | KeyCode::Down | KeyCode::Char(' ')
                    if explorer.replay_position < last =>
                {
                    explorer.replay_position += 1;
                    explorer.current = prepared.trace[explorer.replay_position].0.clone();
                }
                KeyCode::Char('p') | KeyCode::Up if explorer.replay_position > 0 => {
                    explorer.replay_position -= 1;
                    explorer.current = prepared.trace[explorer.replay_position].0.clone();
                }
                KeyCode::Char('f') => {
                    enter_free_exploration(
                        terminal,
                        explorer.current.clone(),
                        &prepared.spec,
                        &mut prepared.env,
                        &prepared.defs,
                    )?;
                }
                _ => {}
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn show_error(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    beat: &Beat,
    beat_index: usize,
    beat_total: usize,
    variant_name: &str,
    variant_total: usize,
    message: &str,
) -> io::Result<PresentNav> {
    loop {
        terminal.draw(|f: &mut Frame| {
            let lines = vec![
                Line::from(format!(
                    "Beat {}/{}: {}",
                    beat_index + 1,
                    beat_total,
                    beat.title
                )),
                Line::from(""),
                Line::from(Span::styled(
                    format!("variant {} failed to prepare:", variant_name),
                    Style::default().fg(Color::Red).add_modifier(Modifier::BOLD),
                )),
                Line::from(Span::styled(
                    message.to_string(),
                    Style::default().fg(Color::Yellow),
                )),
                Line::from(""),
                Line::from("←/→ beat   q quit"),
            ];
            let widget = Paragraph::new(lines)
                .block(Block::default().borders(Borders::ALL).title(" Error "))
                .wrap(Wrap { trim: true });
            f.render_widget(widget, f.area());
        })?;

        if let Event::Key(key) = event::read()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }
            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(PresentNav::Quit),
                KeyCode::Right => return Ok(PresentNav::NextBeat),
                KeyCode::Left => return Ok(PresentNav::PrevBeat),
                KeyCode::Char('v') | KeyCode::Tab if variant_total > 1 => {
                    return Ok(PresentNav::NextVariant);
                }
                _ => {}
            }
        }
    }
}

fn prepare_variant(dir: &Path, beat: &Beat, variant: &Variant) -> Result<PreparedVariant, String> {
    let constants = parse_variant_constants(variant)?;
    let spec_path = dir.join(&variant.spec);
    let config = variant.config.as_ref().map(|c| dir.join(c));
    let prepared =
        prepare_from_path(&spec_path, config.as_deref(), &constants).map_err(|e| e.to_string())?;
    let (env, defs) = prepare_spec(
        &prepared.spec,
        &prepared.domains,
        Some(&prepared.spec_path),
        true,
    )
    .map_err(|e| format!("prepare spec failed: {:?}", e))?;
    let vars = prepared.spec.vars.clone();
    let trace = build_trace(beat, dir, &prepared.spec, &env, &defs, &vars)?;
    if trace.is_empty() {
        return Err("beat produced an empty trace".to_string());
    }
    Ok(PreparedVariant {
        spec: prepared.spec,
        env,
        defs,
        trace,
    })
}

fn build_trace(
    beat: &Beat,
    dir: &Path,
    spec: &Spec,
    env: &Env,
    defs: &Definitions,
    vars: &[Arc<str>],
) -> Result<Trace, String> {
    if !beat.scenario.is_empty() {
        let scenario = parse_scenario(&beat.scenario.join("\n"))
            .map_err(|e| format!("scenario parse error: {}", e))?;
        let result = execute_scenario_with(spec, &scenario, env, defs)
            .map_err(|e| format!("scenario error: {:?}", e))?;
        Ok(result
            .states
            .iter()
            .enumerate()
            .map(|(idx, (step, state, _))| (state.clone(), step_action(idx, step)))
            .collect())
    } else if let Some(replay) = &beat.replay {
        load_replay_trace(&dir.join(replay), vars)
    } else {
        Err("beat has neither scenario nor replay".to_string())
    }
}

fn step_action(idx: usize, step: &ScenarioStep) -> Option<Arc<str>> {
    if idx == 0 {
        return None;
    }
    match step {
        ScenarioStep::Action { name, .. } => Some(name.clone()),
        ScenarioStep::Condition(_) => Some(Arc::from("step")),
    }
}

fn load_replay_trace(path: &Path, vars: &[Arc<str>]) -> Result<Trace, String> {
    let contents = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read replay {}: {}", path.display(), e))?;
    let json: serde_json::Value =
        serde_json::from_str(&contents).map_err(|e| format!("replay parse error: {}", e))?;
    let arr = json
        .get("trace")
        .and_then(|t| t.as_array())
        .ok_or_else(|| "replay file missing 'trace' array".to_string())?;

    let mut trace = Vec::new();
    for (idx, entry) in arr.iter().enumerate() {
        let state = entry
            .get("state")
            .and_then(|s| json_to_state(s, vars))
            .ok_or_else(|| format!("replay trace[{}] state could not be parsed", idx))?;
        let action = if idx == 0 {
            None
        } else {
            Some(
                entry
                    .get("action")
                    .and_then(|a| a.as_str())
                    .map(Arc::from)
                    .unwrap_or_else(|| Arc::from("step")),
            )
        };
        trace.push((state, action));
    }
    Ok(trace)
}
