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
        CheckSpecInput, CheckSpecOutput, ListInvariantsInput, ListInvariantsOutput,
        ReplayScenarioInput, ReplayScenarioOutput, ValidateSpecInput, ValidateSpecOutput,
    },
};

#[derive(Clone)]
struct TlaMcpServer;

#[tool_router]
impl TlaMcpServer {
    #[tool(
        description = "Parse a TLA+ spec, return a structured summary (vars, constants with resolved values, detected invariants, init/next presence, definition_count) or a parse/config error with source span. Call this after EVERY edit to a .tla file AND before each check_spec call. The returned `constants` array shows each declared CONSTANT and the value it resolves to (from cfg directives + your `constants` input). EYEBALL THE VALUES — a single constant that's much larger than the others is the most common cause of timeouts and state-space blowup. The parser silently skips operator bodies it can't parse, so an invariant whose body has a typo will simply not appear in `spec.invariants` — `check_spec` would then 'pass' without ever checking it. If an invariant name you expected is missing, the operator's body has an error or the name does not match auto-detection (Inv*, TypeOK*, NotSolved*)."
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
        - status='limit_reached': budget exhausted with `limit` ('max_states', 'max_depth', or 'max_seconds'). NOT a pass; inconclusive. Look at `stats.states_explored` and `stats.elapsed_secs` to gauge whether to grow the budget or shrink the state space (smaller constants, `symmetry` for interchangeable model values, `state_constraint` to prune).\n\
        - status='error': structured failure with `phase` (parse/config/constant/init/next/invariant/io/internal), message, optional source span.\n\
        Start small: max_states=10000, max_depth=50, max_seconds=30, smallest non-trivial constants (Procs='{p1,p2}'). Most algorithmic bugs surface at 2-3 instances; large constants are for confidence, not discovery."
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
        description = "Replay a guided scenario through a spec, step by step. Each scenario line is `step: <TLA+ expression>` — the checker picks the unique next-state transition that satisfies the expression (unprimed vars refer to the current state, primed vars `x'` to the candidate next state). Returns the same StateSnapshot shape as check_spec, plus per-step `changes` strings showing which variables flipped. Use this for teaching specific failure paths, reproducing user-reported traces, or verifying a fix exercises the exact transition you expect. status='failed' means no transition satisfied a step — the response includes `available_actions` at that point so you can diagnose the mismatch."
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
            • Model checking is bounded. Passing at small constants does not prove the algorithm correct for all sizes. Prefer phrasing like 'verified for these constants' over 'proven correct.'"
                .to_string(),
        );
        info
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let running = TlaMcpServer.serve(stdio()).await?;
    running.waiting().await?;
    Ok(())
}
