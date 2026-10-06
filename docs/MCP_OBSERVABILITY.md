# tla-mcp Observability and Diagnostics

Tracking document for improvements to `tla-mcp` so callers can predict, observe,
and bound model-checking runs instead of waiting for opaque timeouts.

## Motivation

A real session ran `check_spec` against a Raft-style spec at `MaxLogLen=2` with
3 peers. The previous run at `MaxLogLen=1` had completed 10 405 states in 64
seconds (~6 ms/state). The `MaxLogLen=2` run returned `[Tool result missing due
to internal error]` after wall-clocking past the MCP client timeout. The caller
had no signal whether the run was making progress, stuck, about to OOM, or
already finished.

Rough back-of-envelope: going from `MaxLogLen=1` to `2` multiplies per-peer log
content by the entry cardinality (~3 entries → 9 possible contents per peer),
and cross-peer combinations multiply. Estimate: 100 K to 1 M reachable states,
several minutes to tens of minutes wall time. The caller picked a 1 M `max_states`
budget speculatively. A disciplined workflow would run small first, derive a
states-per-second and branching factor, project the larger run, and either
shrink constants or grow budget on evidence.

The tool should make that workflow easy by default.

## Improvement items

Status legend: ✅ done · 🔭 follow-up

### ✅ #5: Structured timeout

`max_seconds` already flows through:

- `checker::check_with_state_vars` — checked at each state-iteration boundary
- `checker::check_liveness_properties` — checked during the liveness phase
- `CheckResult::MaxTimeExceeded(stats)` carries partial stats
- `mcp::runner` — maps it to `CheckOutcome::LimitReached { limit: MaxSeconds, stats }`

A `max_seconds` limit can therefore come from the liveness phase after the
state search finished, in which case the safety result is complete and only the
liveness analysis ran out of time.

**Gap:** the check fires only between states (and between liveness steps). A
single `next_states` call with high fanout can exceed `max_seconds` without
returning. Per-state evaluation is not interruptible. This is documented in the
tool description so callers know that `max_seconds` is a soft bound at state
boundaries.

What `[Tool result missing due to internal error]` means in practice: the MCP
client (or the network/process boundary) gave up before the checker did.
`max_seconds` should always be set below the client's tolerance.

### ✅ #7: Per-action transition counts

`Transition.action: Option<Arc<str>>` carries the disjunct label, and
transitions are bucketed by it:

- `CheckStats.transitions_by_action: BTreeMap<Option<Arc<str>>, usize>`,
  incremented alongside `stats.transitions`
- surfaced as `stats.actions: [{name, transitions}]` in the MCP output, and
  pointed to by the `check_spec` description

Lets the caller see "70% of transitions came from `Receive`" and target the
worst-offending action. TLC has the same view in its stdout; this exposes it
structurally.

### ✅ #3: Bounded Nat in TypeOK

`seq: Nat` in a TypeOK is essentially unbounded for TLC. By default tla-rs
bounds `Nat` to `0..100` and `Int` to `-100..100`, so `x \in Nat` is FALSE once
`x` passes 100: TypeOK reports a false violation and quantifiers over `Nat` miss
larger values. Symbolic integers are opt-in (MCP `symbolic_integers`, cfg
`SYMBOLIC_INTEGERS TRUE` or `--symbolic-integers`) and make `Nat`/`Int` infinite
sets decided by membership. The `validate_spec` tool description recommends
`seq: 0..MaxSeq` (or similar), which is both correct and cheaper to check, so
the caller sees it before launching a slow run.

### ✅ #4: Budget advisories

There are intentionally no defaults — the caller must budget `max_states`,
`max_depth`, and `max_seconds` upfront. Budgets that are almost always a
footgun on an unfamiliar spec are surfaced in
`CheckSpecOutput.advisories: Vec<String>`, populated before the run:

- `max_depth > 100`: "most algorithmic bugs surface at depth < 50"
- `max_states > 1,000,000`: start with smaller constants and grow the budget
  on evidence

Still open: large-constant detection (warn when a single int/set constant is
much bigger than its peers). The `validate_spec` description asks the caller to
eyeball the resolved constants for this in the meantime.

### 🔭 #1: Pre-flight branching-factor estimator

After `Init` enumeration, the checker knows the initial-state count and could
sample a small fanout (run BFS for 100 states, measure transitions/state).
Project against `max_states` and refuse (or strongly warn) when the upper bound
crosses the budget.

A separate `dry_run` tool, or an opt-in field on `check_spec` (e.g., `dry_run:
true` returning only the projection), keeps the contract clean.

Not implemented — needs a small API design pass.

### 🔭 #2: Progress streaming

The current `check_spec` is one-shot — caller waits for the entire run. For
runs >30 s the caller has no signal. Periodic progress events (states/sec,
current depth, distinct states found) via MCP notifications would let the
caller decide to abort early.

Requires investigation: `rmcp` notification capability, whether the MCP spec
supports server-initiated progress messages, and how tokio's
`spawn_blocking` interacts with notification emission. Larger scope, not
implemented.

### 🔭 #6: Symmetry static check

When peer-like model values appear in ordering ops (`<`, `>`, `<=`, `>=`),
`SYMMETRY Permutations(Peers)` silently produces wrong answers because the
ordering relation is not symmetric. Detectable by walking the AST and flagging
ordering ops whose operand types could resolve to a value from a symmetric
constant.

Not implemented — needs type inference or constant-flow analysis the checker
doesn't do.

## Notes on workflow

The disciplined sequence the caller used after the timeout:

1. Run at smallest non-trivial constants.
2. Read `stats.states_explored`, `stats.transitions`, `stats.elapsed_secs`.
3. Compute branching factor (`transitions / states_explored`) and rate
   (`states_explored / elapsed_secs`).
4. Project the larger run.
5. Grow `max_states` / `max_seconds` on evidence — or shrink constants.

The `check_spec` description already gives the formulas for steps 3-4; #1 and
#2 above would compute them instead of leaving them to the caller.
