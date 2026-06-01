use rmcp::{
    ErrorData as McpError, ServerHandler, ServiceExt,
    handler::server::wrapper::{Json, Parameters},
    model::{Implementation, ServerCapabilities, ServerInfo},
    tool, tool_handler, tool_router,
    transport::stdio,
};
use tla_checker::mcp::{
    runner,
    schema::{
        AppendBeatInput, AppendBeatOutput, CheckSpecInput, CheckSpecOutput, ExportDemoDocInput,
        ExportDemoDocOutput, ExportDemoHtmlInput, ExportDemoHtmlOutput, ListInvariantsInput,
        ListInvariantsOutput, ReplayScenarioInput, ReplayScenarioOutput, ValidateDemoInput,
        ValidateDemoOutput, ValidateSpecInput, ValidateSpecOutput,
    },
};

#[derive(Clone)]
struct TlaMcpServer;

#[tool_router]
impl TlaMcpServer {
    #[tool(
        description = "Parse a TLA+ spec, return a structured summary (vars, constants with resolved values, detected invariants, init/next presence, definition_count) or a parse/config error with source span. Call this after EVERY edit to a .tla file AND before each check_spec call. The returned `constants` array shows each declared CONSTANT and the value it resolves to (from cfg directives + your `constants` input). EYEBALL THE VALUES — a single constant that's much larger than the others is the most common cause of timeouts and state-space blowup. The parser silently skips operator bodies it can't parse, so an invariant whose body has a typo will simply not appear in `spec.invariants` — `check_spec` would then 'pass' without ever checking it. If an invariant name you expected is missing, the operator's body has an error or the name does not match auto-detection (Inv*, TypeOK*, NotSolved*).\n\nBOUNDED TYPES IN TypeOK: variables declared as `seq: Nat` or `seq: Seq(T)` make the variable's type domain effectively unbounded for the checker — TypeOK will still hold for the reachable subspace, but the diagnostic cost of containment checks balloons. Prefer bounded forms like `seq: 0..MaxSeq` or `seq: [1..MaxSeq -> T]` so the universe being checked is finite and small."
    )]
    async fn validate_spec(
        &self,
        Parameters(input): Parameters<ValidateSpecInput>,
    ) -> Result<Json<ValidateSpecOutput>, McpError> {
        Ok(Json(runner::validate_spec(&input)))
    }

    #[tool(
        description = "Return the detected invariants for a spec. An invariant is any zero-arg definition whose name matches Inv*, TypeOK*, NotSolved*, plus anything declared via cfg INVARIANT directive. Use this BEFORE suggesting a new invariant (to avoid duplicating or shadowing) and as a sanity check after renaming operators — the result reflects exactly what check_spec will verify."
    )]
    async fn list_invariants(
        &self,
        Parameters(input): Parameters<ListInvariantsInput>,
    ) -> Result<Json<ListInvariantsOutput>, McpError> {
        Ok(Json(runner::list_invariants(&input)))
    }

    #[tool(
        description = "Run the TLA+ model checker. REQUIRED: max_states, max_depth, AND max_seconds — no defaults, you must budget all three upfront. ALWAYS call validate_spec first and inspect the returned `constants` — a single constant much larger than its peers is the most common cause of timeouts. Optional booleans `allow_deadlock` and `check_liveness` default to the cfg's setting; omit to defer, pass true/false to override. Returns one of:\n\
        - status='ok': full reachable state space exhausted, no invariant violated. This is 'passed.'\n\
        - status='invariant_violation': has `invariant`, `trace` (states), `actions` (action that produced each state, null for initial). The bug is almost always in the LAST transition — compare `trace[len-2]` and `trace[len-1]` `vars.display`, and read `actions[len-1]` to see which action fired.\n\
        - status='deadlock': terminal state, allow_deadlock was false. Inspect the last state and ask: what action SHOULD have been enabled here?\n\
        - status='liveness_violation': only when check_liveness=true. Returns prefix + cycle of states the spec gets stuck in.\n\
        - status='limit_reached': budget exhausted with `limit` ('max_states', 'max_depth', or 'max_seconds'). NOT a pass; inconclusive. Look at `stats.states_explored` and `stats.elapsed_secs` to gauge whether to grow the budget or shrink the state space (smaller constants, `symmetry` for interchangeable model values, `state_constraint` to prune). `stats.actions` shows the per-action transition counts — the worst offender is the action worth constraining or simplifying first.\n\
        - status='error': structured failure with `phase` (parse/config/constant/init/next/invariant/io/internal), message, optional source span.\n\
        `max_seconds` is a SOFT bound checked between states. A single `next_states` call with very large fanout can blow past it without returning. Always set `max_seconds` well under your MCP client's tolerance. The top-level `advisories` array surfaces concerns about your budget (e.g., `max_depth` over 100) so you can correct them before re-running.\n\
        Start small: max_states=10000, max_depth=50, max_seconds=30, smallest non-trivial constants (Procs='{p1,p2}'). Most algorithmic bugs surface at 2-3 instances; large constants are for confidence, not discovery. When stepping up constants, project from a small run first: rate = states_explored / elapsed_secs and fanout = transitions / states_explored let you estimate the next run's cost before launching."
    )]
    async fn check_spec(
        &self,
        Parameters(input): Parameters<CheckSpecInput>,
    ) -> Result<Json<CheckSpecOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::check_spec(&input))
            .await
            .map_err(|e| McpError::internal_error(format!("check task join error: {}", e), None))?;
        Ok(Json(output))
    }

    #[tool(
        description = "Replay a guided scenario through a spec, step by step. Each scenario line is either `step: <TLA+ expression>` (the checker picks the next-state transition satisfying the expression — unprimed vars refer to the current state, primed vars `x'` to the candidate next state, and cfg/`constants` resolve inside the expression) or `action: <Name>` (pin the transition to the named action; optionally `action: <Name>; <expression>` to constrain it further). Prefer `action:` over adding a synthetic tag variable to the spec. Returns the same StateSnapshot shape as check_spec, plus per-step `changes` strings showing which variables flipped. Use this for teaching specific failure paths, reproducing user-reported traces, or verifying a fix exercises the exact transition you expect. status='failed' means no transition satisfied a step — the response includes `available_actions` at that point so you can diagnose the mismatch."
    )]
    async fn replay_scenario(
        &self,
        Parameters(input): Parameters<ReplayScenarioInput>,
    ) -> Result<Json<ReplayScenarioOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::replay_scenario(&input))
            .await
            .map_err(|e| {
                McpError::internal_error(format!("scenario task join error: {}", e), None)
            })?;
        Ok(Json(output))
    }

    #[tool(
        description = "Validate a demo manifest (a JSON or TOML file next to the spec bundling named `variants` and ordered `beats`; humans tend to author TOML, the MCP emits JSON). Runs every beat — each beat is a `scenario` (step:/action: lines) or a `replay`, run against one `variant` or several via `compare` — and checks its `expect`/`expect_per_variant` assertions (`final:` / `all:` / `never:` / `step N:` predicates) against the resulting trace. Returns per-beat, per-variant pass/fail with the full trace, so you can confirm a demo behaves as described WITHOUT re-running replay_scenario by hand and eyeballing each trace. status='passed' (all assertions hold), 'failed' (some assertion false), or 'error' (a beat could not run — bad spec/scenario/variant reference)."
    )]
    async fn validate_demo(
        &self,
        Parameters(input): Parameters<ValidateDemoInput>,
    ) -> Result<Json<ValidateDemoOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::validate_demo(&input))
            .await
            .map_err(|e| {
                McpError::internal_error(format!("validate_demo task join error: {}", e), None)
            })?;
        Ok(Json(output))
    }

    #[tool(
        description = "Append a beat to a demo manifest and validate it in one step. Provide `title`, a `scenario` (step:/action: lines), `variant` OR `compare` (variant names that must already exist in the manifest), an optional `note`, and `expect`/`expect_per_variant` assertions. The beat is run before writing and is only persisted when every assertion passes: if it cannot run (bad scenario/variant) status='error' and nothing is written, and if it runs but an assertion is false status='failed' and nothing is written (the response carries the failing assertions so you can fix `expect` and call again). Set `validate_only: true` to preview the beat's result WITHOUT persisting — use this to iterate on expectations, then call again without it to write the now-passing beat. When persisted, `written` is true; the manifest is rewritten in its own format (a `.toml` file stays TOML, otherwise JSON), so appending to a human's TOML does not clobber it. This is the authoring loop: craft a scenario, append_beat to check + record it, instead of running replay_scenario and hand-maintaining a separate doc."
    )]
    async fn append_beat(
        &self,
        Parameters(input): Parameters<AppendBeatInput>,
    ) -> Result<Json<AppendBeatOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::append_beat(&input))
            .await
            .map_err(|e| {
                McpError::internal_error(format!("append_beat task join error: {}", e), None)
            })?;
        Ok(Json(output))
    }

    #[tool(
        description = "Render a demo manifest to a Markdown walkthrough at `out_path`. Runs every beat and writes a document with each beat's title, note, scenario steps, and the VERIFIED expectation results (✓/✗ per assertion) per variant. The doc is generated and tested — it reflects actual trace outcomes, not hand-written prose — so it stays in sync with the spec. status reflects whether all beats passed; the file is written either way."
    )]
    async fn export_demo_doc(
        &self,
        Parameters(input): Parameters<ExportDemoDocInput>,
    ) -> Result<Json<ExportDemoDocOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::export_demo_doc(&input))
            .await
            .map_err(|e| {
                McpError::internal_error(format!("export_demo_doc task join error: {}", e), None)
            })?;
        Ok(Json(output))
    }

    #[tool(
        description = "Render a demo manifest to a self-contained HTML walkthrough at `out_path`. Same content as export_demo_doc but as a single offline file (no external resources, nothing leaves the file) with an interactive viewer: step through each beat, compare variants side by side, see per-step state diffs and the verified ✓/✗ assertions. Set `explorable: true` to also embed the wasm model-checking engine, turning the file into a live state explorer — step through enabled actions from any state (number-key hotkeys, actions grouped by name) and see live invariant results, all in the browser. Use this to share a runnable demo for a talk or review without requiring the recipient to install tla. status reflects whether all beats passed; the file is written either way."
    )]
    async fn export_demo_html(
        &self,
        Parameters(input): Parameters<ExportDemoHtmlInput>,
    ) -> Result<Json<ExportDemoHtmlOutput>, McpError> {
        let output = tokio::task::spawn_blocking(move || runner::export_demo_html(&input))
            .await
            .map_err(|e| {
                McpError::internal_error(format!("export_demo_html task join error: {}", e), None)
            })?;
        Ok(Json(output))
    }
}

#[tool_handler]
impl ServerHandler for TlaMcpServer {
    fn get_info(&self) -> ServerInfo {
        let mut implementation = Implementation::default();
        implementation.name = "tla-mcp".to_string();
        implementation.title = Some("TLA+ Model Checker MCP Server".to_string());
        implementation.version = env!("CARGO_PKG_VERSION").to_string();
        implementation.website_url = Some("https://github.com/fabracht/tla-rs".to_string());

        let mut info = ServerInfo::default();
        info.capabilities = ServerCapabilities::builder().enable_tools().build();
        info.server_info = implementation;
        info.instructions = Some(
            "TLA+ model checker as MCP tools. Behaviors to follow:\n\
            \n\
            • `limit_reached` is NOT a pass. It means the budget (max_states / max_depth) was exhausted before exploring the full reachable state space — treat as inconclusive. Either grow the budget OR shrink the state space (smaller constants, enable `symmetry`) before drawing conclusions.\n\
            \n\
            • Always validate_spec after editing a .tla file. The parser is tolerant: malformed operator bodies become SILENT omissions, so a spec can 'parse cleanly' while missing the operator you cared about. Cross-check the returned `spec.invariants` list against what you expected.\n\
            \n\
            • Bugs are local. Counterexample traces can be long, but the rule violation is almost always in the LAST transition — compare `trace[len-2]` vs `trace[len-1]` using their `display` fields, and inspect `actions[len-1]` for the action that fired. Reasoning about the whole trace usually wastes effort.\n\
            \n\
            • Defer to the cfg by default. The server auto-loads `<spec>.cfg` if present; its CONSTANTS / INVARIANTS / SYMMETRY / CHECK_DEADLOCK directives apply. Only pass `allow_deadlock` / `check_liveness` to override what the cfg says — omit them to inherit.\n\
            \n\
            • Boundary values catch bugs. Run with the smallest non-trivial constants first (2-3 processes, MaxBuffer=1 or 2). Most algorithmic bugs surface at small sizes; large constants are for building confidence, not for discovering bugs.\n\
            \n\
            • Safety ≠ liveness. Invariants (state predicates) are safety. Fairness, `<>`, `~>`, `WF_vars` are liveness — require `check_liveness: true` and run a different analysis (SCC). 'Spec passes safety check' does NOT mean 'spec satisfies its liveness property.'\n\
            \n\
            • Model checking is bounded. Passing at small constants does not prove the algorithm correct for all sizes. Prefer phrasing like 'verified for these constants' over 'proven correct.'\n\
            \n\
            • Demos read best on named-action specs. validate_demo / append_beat / export_demo_* pin each scenario step with `action: <Name>` — one self-describing step per move, and one hotkeyed explorer row per action. A spec whose `Next` is a single `\\E ...` quantifier has no action to name, so steps fall back to `step:` predicates that re-state the next state and the explorer collapses every transition under one row — it still works, just reads worse. When authoring a demo, prefer lifting common moves into named operators over adding a synthetic tag variable, and expose the key property as a named definition (e.g. `Solved == ...`) so beats can assert `final: Solved` and the explorer shows it live."
                .to_string(),
        );
        info
    }
}

#[cfg(target_os = "linux")]
fn request_parent_death_signal() {
    unsafe {
        libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGTERM);
    }
}

#[cfg(not(target_os = "linux"))]
fn request_parent_death_signal() {}

#[cfg(unix)]
async fn wait_for_shutdown_signal() -> bool {
    use tokio::signal::unix::{SignalKind, signal};
    let (mut term, mut interrupt) = match (
        signal(SignalKind::terminate()),
        signal(SignalKind::interrupt()),
    ) {
        (Ok(term), Ok(interrupt)) => (term, interrupt),
        _ => return false,
    };
    tokio::select! {
        _ = term.recv() => true,
        _ = interrupt.recv() => true,
    }
}

#[cfg(not(unix))]
async fn wait_for_shutdown_signal() -> bool {
    tokio::signal::ctrl_c().await.is_ok()
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    request_parent_death_signal();

    tokio::spawn(async {
        if wait_for_shutdown_signal().await {
            std::process::exit(0);
        }
    });

    let running = TlaMcpServer.serve(stdio()).await?;
    running.waiting().await?;
    std::process::exit(0);
}
