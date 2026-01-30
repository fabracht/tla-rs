use std::fs;
use std::io;
use std::path::Path;
use std::sync::Arc;

use crate::ast::{Env, Spec, State, Transition, TransitionWithGuards, Value, VarChange};
use crate::checker::format_value;
use crate::eval::{Definitions, eval, make_primed_names, next_states, next_states_with_guards};

use super::serialize::{json_to_state, state_to_json};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum InputMode {
    Normal,
    Repl,
    Trace,
    Hypothesis,
    Walk,
    StepUntil,
}

pub(crate) struct ExplorerState {
    pub(crate) current: State,
    pub(crate) history: Vec<(State, Option<Arc<str>>)>,
    pub(crate) available_actions: Vec<Transition>,
    pub(crate) available_actions_with_guards: Vec<TransitionWithGuards>,
    pub(crate) selected_action: usize,
    pub(crate) repl_input: String,
    pub(crate) repl_output: Option<String>,
    pub(crate) input_mode: InputMode,
    pub(crate) status_message: Option<(String, bool)>,
    pub(crate) var_changes: Vec<VarChange>,
    pub(crate) trace_input: String,
    pub(crate) trace_output: Option<Vec<VarChange>>,
    pub(crate) hypothesis_input: String,
    pub(crate) hypothesis_output: Option<String>,
    pub(crate) walk_input: String,
    pub(crate) step_until_input: String,
    pub(crate) show_guards: bool,
    pub(crate) replay_mode: bool,
    pub(crate) replay_trace: Vec<(State, Option<Arc<str>>)>,
    pub(crate) replay_position: usize,
}

impl ExplorerState {
    pub(crate) fn new(
        initial: State,
        actions: Vec<Transition>,
        actions_with_guards: Vec<TransitionWithGuards>,
    ) -> Self {
        Self {
            current: initial,
            history: Vec::new(),
            available_actions: actions,
            available_actions_with_guards: actions_with_guards,
            selected_action: 0,
            repl_input: String::new(),
            repl_output: None,
            input_mode: InputMode::Normal,
            status_message: None,
            var_changes: Vec::new(),
            trace_input: String::new(),
            trace_output: None,
            hypothesis_input: String::new(),
            hypothesis_output: None,
            walk_input: String::new(),
            step_until_input: String::new(),
            show_guards: false,
            replay_mode: false,
            replay_trace: Vec::new(),
            replay_position: 0,
        }
    }

    pub(crate) fn take_action(&mut self, spec: &Spec, env: &mut Env, defs: &Definitions) {
        self.take_action_at(self.selected_action, spec, env, defs);
    }

    pub(crate) fn take_action_at(
        &mut self,
        action_idx: usize,
        spec: &Spec,
        env: &mut Env,
        defs: &Definitions,
    ) {
        if self.available_actions.is_empty() {
            self.status_message = Some(("No actions available (deadlock)".into(), true));
            return;
        }

        let transition = self.available_actions[action_idx].clone();
        let prev_state = self.current.clone();
        let action_name = transition.action.clone();
        let state_idx = self.history.len() + 1;

        for (vi, var) in spec.vars.iter().enumerate() {
            let old_val = prev_state.values.get(vi);
            let new_val = transition.state.values.get(vi);
            if old_val != new_val
                && let (Some(old), Some(new)) = (old_val, new_val)
            {
                self.record_value_changes(
                    state_idx,
                    var.to_string(),
                    old,
                    new,
                    action_name.clone(),
                );
            }
        }

        self.history.push((prev_state, action_name));
        self.current = transition.state.clone();
        self.selected_action = 0;

        self.refresh_actions(spec, env, defs);
    }

    fn refresh_actions(&mut self, spec: &Spec, env: &mut Env, defs: &Definitions) {
        let primed_vars = make_primed_names(&spec.vars);
        match next_states(
            &spec.next,
            &self.current,
            &spec.vars,
            &primed_vars,
            env,
            defs,
        ) {
            Ok(actions) => {
                self.available_actions = actions.clone();
                match next_states_with_guards(
                    &spec.next,
                    &self.current,
                    &spec.vars,
                    &primed_vars,
                    env,
                    defs,
                ) {
                    Ok(guards) => self.available_actions_with_guards = guards,
                    Err(_) => {
                        self.available_actions_with_guards = actions
                            .iter()
                            .map(|t| TransitionWithGuards {
                                transition: t.clone(),
                                guards: Vec::new(),
                                parameter_bindings: Vec::new(),
                            })
                            .collect()
                    }
                }
                self.status_message = None;
            }
            Err(e) => {
                self.available_actions = Vec::new();
                self.available_actions_with_guards = Vec::new();
                self.status_message = Some((format!("Error computing next states: {:?}", e), true));
            }
        }
    }

    fn record_value_changes(
        &mut self,
        state_idx: usize,
        path: String,
        old_val: &Value,
        new_val: &Value,
        action: Option<Arc<str>>,
    ) {
        match (old_val, new_val) {
            (Value::Fn(old_map), Value::Fn(new_map)) => {
                for (k, v) in new_map {
                    let key_str = format_value(k);
                    let new_path = format!("{}[{}]", path, key_str);
                    match old_map.get(k) {
                        Some(old_v) if old_v != v => {
                            self.record_value_changes(
                                state_idx,
                                new_path,
                                old_v,
                                v,
                                action.clone(),
                            );
                        }
                        None => {
                            self.var_changes.push(VarChange {
                                state_idx,
                                path: new_path,
                                old_value: Value::Set(std::collections::BTreeSet::new()),
                                new_value: v.clone(),
                                action: action.clone(),
                            });
                        }
                        _ => {}
                    }
                }
                for k in old_map.keys() {
                    if !new_map.contains_key(k) {
                        let key_str = format_value(k);
                        let new_path = format!("{}[{}]", path, key_str);
                        self.var_changes.push(VarChange {
                            state_idx,
                            path: new_path,
                            old_value: old_map.get(k).cloned().unwrap_or(Value::Bool(false)),
                            new_value: Value::Set(std::collections::BTreeSet::new()),
                            action: action.clone(),
                        });
                    }
                }
            }
            (Value::Record(old_rec), Value::Record(new_rec)) => {
                for (k, v) in new_rec {
                    let new_path = format!("{}.{}", path, k);
                    match old_rec.get(k) {
                        Some(old_v) if old_v != v => {
                            self.record_value_changes(
                                state_idx,
                                new_path,
                                old_v,
                                v,
                                action.clone(),
                            );
                        }
                        None => {
                            self.var_changes.push(VarChange {
                                state_idx,
                                path: new_path,
                                old_value: Value::Bool(false),
                                new_value: v.clone(),
                                action: action.clone(),
                            });
                        }
                        _ => {}
                    }
                }
            }
            _ => {
                self.var_changes.push(VarChange {
                    state_idx,
                    path,
                    old_value: old_val.clone(),
                    new_value: new_val.clone(),
                    action,
                });
            }
        }
    }

    pub(crate) fn backtrack(&mut self, spec: &Spec, env: &mut Env, defs: &Definitions) {
        if let Some((prev_state, _)) = self.history.pop() {
            let current_state_idx = self.history.len() + 1;
            self.var_changes.retain(|c| c.state_idx < current_state_idx);

            self.current = prev_state;
            self.selected_action = 0;

            self.refresh_actions(spec, env, defs);
        }
    }

    pub(crate) fn reset(
        &mut self,
        initial: State,
        actions: Vec<Transition>,
        actions_with_guards: Vec<TransitionWithGuards>,
    ) {
        self.current = initial;
        self.history.clear();
        self.available_actions = actions;
        self.available_actions_with_guards = actions_with_guards;
        self.selected_action = 0;
        self.status_message = None;
        self.var_changes.clear();
        self.trace_output = None;
    }

    pub(crate) fn compute_trace(&self, path_filter: &str) -> Vec<VarChange> {
        let filter = path_filter.trim();
        if filter.is_empty() {
            self.var_changes.clone()
        } else {
            self.var_changes
                .iter()
                .filter(|c| c.path.starts_with(filter) || c.path == filter)
                .cloned()
                .collect()
        }
    }

    pub(crate) fn select_next(&mut self) {
        if !self.available_actions.is_empty() {
            self.selected_action = (self.selected_action + 1) % self.available_actions.len();
        }
    }

    pub(crate) fn select_prev(&mut self) {
        if !self.available_actions.is_empty() {
            self.selected_action = (self.selected_action + self.available_actions.len() - 1)
                % self.available_actions.len();
        }
    }

    pub(crate) fn random_walk(
        &mut self,
        steps: usize,
        spec: &Spec,
        env: &mut Env,
        defs: &Definitions,
    ) {
        for i in 0..steps {
            if self.available_actions.is_empty() {
                self.status_message = Some((format!("Deadlock after {} steps", i), true));
                return;
            }
            let idx = fastrand::usize(..self.available_actions.len());
            self.take_action_at(idx, spec, env, defs);
        }
        self.status_message = Some((format!("Walked {} steps", steps), false));
    }

    pub(crate) fn step_until(
        &mut self,
        condition: &crate::ast::Expr,
        max_steps: usize,
        spec: &Spec,
        env: &mut Env,
        defs: &Definitions,
    ) {
        for i in 0..max_steps {
            let mut eval_env = env.clone();
            for (vi, var) in spec.vars.iter().enumerate() {
                if let Some(val) = self.current.values.get(vi) {
                    eval_env.insert(var.clone(), val.clone());
                }
            }
            match eval(condition, &mut eval_env, defs) {
                Ok(Value::Bool(true)) => {
                    self.status_message = Some((format!("Condition met after {} steps", i), false));
                    return;
                }
                Ok(Value::Bool(false)) => {}
                Ok(other) => {
                    self.status_message = Some((
                        format!("Condition must be Bool, got {}", format_value(&other)),
                        true,
                    ));
                    return;
                }
                Err(e) => {
                    self.status_message = Some((format!("Eval error: {:?}", e), true));
                    return;
                }
            }
            if self.available_actions.is_empty() {
                self.status_message = Some((
                    format!("Deadlock after {} steps, condition not met", i),
                    true,
                ));
                return;
            }
            let idx = fastrand::usize(..self.available_actions.len());
            self.take_action_at(idx, spec, env, defs);
        }
        self.status_message = Some((format!("Condition not met after {} steps", max_steps), true));
    }

    pub(crate) fn save_trace(
        &self,
        path: &Path,
        vars: &[Arc<str>],
        initial: &State,
    ) -> io::Result<()> {
        let mut trace_entries: Vec<serde_json::Value> = Vec::new();
        trace_entries.push(serde_json::json!({
            "action": serde_json::Value::Null,
            "state": state_to_json(initial, vars)
        }));
        for (state, action) in &self.history {
            trace_entries.push(serde_json::json!({
                "action": action.as_ref().map(|a| a.to_string()),
                "state": state_to_json(state, vars)
            }));
        }
        trace_entries.push(serde_json::json!({
            "action": serde_json::Value::Null,
            "state": state_to_json(&self.current, vars)
        }));

        let trace_json = serde_json::json!({
            "vars": vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
            "trace": trace_entries
        });

        let content = serde_json::to_string_pretty(&trace_json).map_err(io::Error::other)?;
        fs::write(path, content)
    }

    pub(crate) fn load_trace(
        path: &Path,
        spec: &Spec,
        env: &mut Env,
        defs: &Definitions,
        initial: &State,
    ) -> io::Result<Self> {
        let content = fs::read_to_string(path)?;
        let json: serde_json::Value = serde_json::from_str(&content)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let trace_arr = json
            .get("trace")
            .and_then(|t| t.as_array())
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing trace array"))?;

        if trace_arr.is_empty() {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "empty trace"));
        }

        let mut history: Vec<(State, Option<Arc<str>>)> = Vec::new();
        let mut prev_state = initial.clone();

        for (i, entry) in trace_arr.iter().enumerate().skip(1) {
            let action = entry.get("action").and_then(|a| a.as_str()).map(Arc::from);
            let state = entry
                .get("state")
                .and_then(|s| json_to_state(s, &spec.vars))
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, "invalid state in trace")
                })?;

            if i < trace_arr.len() - 1 {
                history.push((prev_state.clone(), action));
            }
            prev_state = state;
        }

        let current = prev_state;
        let primed_vars = make_primed_names(&spec.vars);
        let available_actions =
            next_states(&spec.next, &current, &spec.vars, &primed_vars, env, defs)
                .map_err(|e| io::Error::other(format!("{:?}", e)))?;
        let available_actions_with_guards =
            next_states_with_guards(&spec.next, &current, &spec.vars, &primed_vars, env, defs)
                .unwrap_or_else(|_| {
                    available_actions
                        .iter()
                        .map(|t| TransitionWithGuards {
                            transition: t.clone(),
                            guards: Vec::new(),
                            parameter_bindings: Vec::new(),
                        })
                        .collect()
                });

        Ok(Self {
            current,
            history,
            available_actions,
            available_actions_with_guards,
            selected_action: 0,
            repl_input: String::new(),
            repl_output: None,
            input_mode: InputMode::Normal,
            status_message: None,
            var_changes: Vec::new(),
            trace_input: String::new(),
            trace_output: None,
            hypothesis_input: String::new(),
            hypothesis_output: None,
            walk_input: String::new(),
            step_until_input: String::new(),
            show_guards: false,
            replay_mode: false,
            replay_trace: Vec::new(),
            replay_position: 0,
        })
    }
}
