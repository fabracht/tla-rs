# Changelog

## [0.6.11] - 2026-07-15

### Added

- `tla` and `tla-mcp` now support `--version` (and `-V`), printing the package version and exiting 0. Previously neither binary could report its own version — `tla --version` failed with `unknown option: --version`, so verifying which build was installed (e.g. after a Homebrew upgrade) meant comparing the binary's SHA256 against the release asset. `tla --help` now lists the flag, and `tla-mcp` handles it before starting the stdio server. Fixes #67.

## [0.6.10] - 2026-07-14

### Added

- `<>[]P` (stable-eventually, "eventually always") is now checked instead of being silently dropped. Previously the temporal-property extractor emitted a warning and discarded the inner expression, so a `SPECIFICATION`/cfg `PROPERTY` of the form `<>[]P` made `check_spec` return a vacuous `ok` without checking anything. The property is now dispatched to a dedicated analysis: `<>[]P` is violated exactly when a reachable fair cycle revisits a `¬P` state, and holds when every fair behavior eventually reaches `P` and stays there.

### Fixed

- Liveness counterexamples now report a real cycle whose steps are actual transitions, instead of the recurrent SCC's state-set rendered in an arbitrary order with fabricated `-->` arrows. The checker extracts an ordered cycle by following genuine edges back to a witnessing state (preferring real progress over the always-present stutter self-loop, and falling back to the minimal single-state cycle when stuttering is the only recurrence). The fairness check still runs over the full recurrent set, so detection is unchanged — only the displayed trace is now faithful. Fixes #64.
- Weak/strong fairness (`WF_v(A)` / `SF_v(A)`) now treats fairness as being about `⟨A⟩_v ≡ A ∧ (vars' ≠ vars)` rather than about `A` merely admitting a stuttering step. Previously, when a fair action allowed a stutter (e.g. `A == x' \in {x, x+1}`), the checker counted the `x'=x` self-loop as "A taken" and treated a stutter-forever cycle as fair, reporting a spurious `liveness_violation` for a property that actually holds under weak fairness. Both sides of the fairness check now ignore stuttering steps: an action is "taken" only on a state-changing edge, and "enabled" for fairness only when a state-changing successor satisfies it (so weak fairness on a pure-stutter action is correctly vacuous rather than spuriously forcing progress). Fixes #63.
- Liveness checking now models the implicit stuttering that `[][Next]_vars` always permits, matching TLC. Previously the SCC analysis walked only explicit transitions, so a state whose sole successor was an *unfair* action was wrongly treated as forced to take it, and infinite stuttering at a non-deadlock state was never considered a behavior. A liveness property whose satisfaction depends on progress being forced — `<>P` with no fairness, or a consumer that can stall forever while only an unfair action is enabled — could therefore return a false `ok`. The liveness graph now adds an implicit stutter self-loop to every state; the existing weak/strong fairness filtering discharges the spurious cycles (a stutter-only cycle is rejected wherever a fair action is enabled), so only genuinely stuck states survive as violations. Modeling a stalling agent no longer requires an explicit `\/ UNCHANGED vars` disjunct.

## [0.6.7] - 2026-07-13

### Fixed

- A temporal `PROPERTY` referenced from a cfg file (e.g. `Eventually1 == <>(x = 1)`) is now routed to the liveness checker instead of being evaluated as a state predicate. Previously the cfg loader pushed the raw property body into the liveness property list without unwrapping its temporal operator, so the checker handed a live `<>`/`~>`/`[]<>` node to the evaluator and aborted with "temporal operator `<>` (eventually) reached eval" — making liveness checking unreachable through a cfg `PROPERTY` (and the `check_spec` MCP tool) even with liveness enabled. cfg properties now pass through the same temporal normalization as the `SPECIFICATION` and parser paths, and quantified temporal properties (`\A s \in S : P(s) ~> Q(s)`) alone are enough to trigger the liveness pass.
- A cfg `PROPERTY` whose definition name ends in `Spec` (e.g. `EventuallySpec == <>(x = 1)`) is no longer extracted into the liveness list twice. The parser already pre-extracts fairness/liveness from any `*Spec`-named definition, and the cfg path now skips re-extraction for those names, matching the `SPECIFICATION` path.
- An existential temporal property `\E i \in S : <>Q(i)` is now checked instead of being silently dropped. It is normalized to the equivalent `<>(\E i \in S : Q(i))` liveness property. Existential temporal shapes that do not reduce this way (e.g. `\E i \in S : P(i) ~> Q(i)`) now emit a warning rather than vanishing without notice, and cfg-application warnings are surfaced through the loaders (both the CLI/library `prepare_from_path` and the MCP runner) instead of being discarded.

## [0.6.6] - 2026-07-06

### Added

- Headless browser smoke test for the exported explorable demo's explorer JavaScript. A Playwright test drives the real embedded wasm engine in Chromium and asserts the runtime behavior the Rust render test can only check as string scaffolding: one action row per enabled-action group, a solo action's number-key hotkey firing the transition and advancing the state, `Backspace` stepping back, and a multi-variant group's hotkey expanding its variant sublist. Runs in a new `explorer-e2e` CI job that builds `tla` with the embedded wasm engine, exports a fixture demo, and runs the test against it.

## [0.6.5] - 2026-07-05

### Fixed

- Liveness checking now enforces `WF_vars`/`SF_vars` fairness against the actual recurring cycles instead of reporting them as violations. Previously a fair action that was continuously enabled but never taken produced a spurious `liveness_violation`, and a fairness check applied to the whole SCC missed unfair sub-cycles nested inside a larger SCC, so a `~>` property that holds under weak fairness could still be reported as violated. The checker now also inspects every violating sub-cycle within an SCC rather than only the first: a genuine fair counterexample is no longer missed when an unfair sub-cycle happens to be found first in the same SCC.
- Quantified fairness `\A s \in S : WF_vars(A(s))` (and the strong-fairness form) is now expanded into per-element constraints using the resolved constants, rather than leaking `WF_vars` into the initial-state predicate and aborting evaluation.
- A universally quantified leads-to property such as `\A s \in S : P(s) ~> Q(s)` now parses with the quantifier body extending across `~>` and is expanded into per-element properties, instead of failing with `undefined variable`.

## [0.6.4] - 2026-06-03

### Changed

- Explorable demo HTML: combinatorial action variants are no longer rendered as one button per concrete transition. When a named action's variants differ only in a few variables' next-state values (e.g. `Reboot == \E v \in 0..MaxTime : wallClock' = v`), the explorer factors them into the effect shared by every variant (shown once) plus one value picker per differing variable. A single varying variable fires on selection; several render as cascading dropdowns — choosing one narrows the others to co-occurring values — plus a "step" button, so a reboot that picks both an offline duration and a boot-time wall clock becomes two dropdowns instead of their cross-product. Groups that don't factor into clean `var = value` dimensions fall back to a capped variant list with "show all". The per-variable next-state values come from the transitions the engine already returns, so no engine change was needed.

## [0.6.3] - 2026-06-01

### Added

- Structural membership for record-type sets. `r \in [f1: T1, f2: T2, ...]` and the type-invariant idiom `vars \subseteq [f1: T1, ...]` are now checked structurally instead of by enumerating the right-hand side, so field types may be infinite — most importantly `Seq(T)`. Membership verifies the value is a record with exactly those fields and that each field value belongs to its type set, recursively (so `SUBSET S`, `[D -> R]`, and `Seq(T)` field types all compose). This unblocks the standard TLA+ type invariant for specs with sequence-valued record fields (e.g. message-queue models), which previously failed with "Seq(S) cannot be enumerated". `\notin` is handled symmetrically.
- cfg `CONSTANT` values and the CLI `-c`/`--constant` flag now accept tuple, record, and function literals: `<<1, 2>>` (tuple), `[hp |-> 100, mp |-> 50]` (record), and `d1 :> 1 @@ d2 :> 2` (function, left-biased on key collisions). All shapes nest inside one another and inside sets. Previously only integers, booleans, strings, model values, and sets were accepted, so specs ported from TLC that relied on function- or record-valued constants could not be configured without rewriting the spec. The set-of-functions form `[S -> T]` remains rejected with a clear error — it is a spec-level expression, not a concrete value.

## [0.6.1] - 2026-06-01

### Changed

- Explorable demo HTML (`--explorable` / `export_demo_html` with `explorable: true`): reworked the in-browser explorer for usability. Enabled actions are now grouped by name — a combinatorial action whose primed variable ranges over many values collapses into one expandable row with a variant count instead of flooding the page with one button per concrete transition. Top-level action rows map to MMORPG-style number-key hotkeys (`1`–`9`, `0`, `-`, `=`); a solo key fires its action, a group key expands it, and `Backspace` steps back. The actions panel is height-capped and scrollable so a large branching factor can't break the layout.

### Removed

- Dropped the explorer's Evaluate/REPL column — it only echoed variables already shown in the State panel. The `explore_eval` WASM binding remains available for embedders. The explorer is now a two-column State + Enabled-actions layout.

## [0.6.0] - 2026-05-29

### Changed

- Performance: state-space generation is substantially faster with identical results. Measured speedups (min of 3 runs): Two-Phase Commit ~2.5x (5 RMs 1.26s->0.50s, 6 RMs 9.22s->3.51s), N-Queens ~1.5x (N=4 0.59s->0.38s), and ~1.6x on the 409k-state TimeIntegrity example (63.9s->39.6s). Allocation churn roughly halved (dhat on N-Queens N=4: 7.74M->3.56M allocations). State counts and counterexample traces are bit-identical across all example and test specs. Four changes drove it: recursive function-application evaluation (no per-call vector), reference-counted collection values, skipping redundant candidate re-inference for actions whose primed variables are independent, and interning identifier and primed-variable names.

### Breaking

- The public `Value` enum now stores its collection payloads behind `Arc`: `Set(Arc<BTreeSet<Value>>)`, `Fn(Arc<BTreeMap<Value, Value>>)`, `Record(Arc<BTreeMap<Arc<str>, Value>>)`, and `Tuple(Arc<Vec<Value>>)`. Cloning a `Value` is now a reference-count bump rather than a deep copy. Pattern matches that bind these payloads now bind `&Arc<...>` (most read-only uses are unaffected via `Deref`); code that mutated or moved out the inner collection should use `Arc::make_mut` / `Arc::unwrap_or_clone`. New constructors `Value::set`, `Value::func`, `Value::record`, and `Value::tuple` wrap a plain collection.

## [0.5.5] - 2026-05-28

### Added

- `export_demo_html` MCP tool gained an `explorable` option (default `false`). When `true`, it embeds the wasm engine in the exported file — the same live in-browser state explorer as the CLI's `tla --present … --export-html … --explorable` — so an agent can hand a user a runnable explorer, not just a static walkthrough. The prebuilt `tla-mcp` release binary is now built with the `embed-wasm` feature so this works out of the box; a `tla-mcp` built without it returns a structured config error when `explorable` is requested.

## [0.5.4] - 2026-05-28

### Fixed

- Release workflow: the `Build WASM engine` job pinned `wasm-bindgen-cli` to a hardcoded version that mismatched the `wasm-bindgen` dependency CI resolved (the repo has no committed `Cargo.lock`), which failed the binary build and skipped the GitHub release for 0.5.3. The CLI version is now derived from the resolved dependency. The 0.5.3 crate was published to crates.io and npm; this release ships the prebuilt `tla`/`tla-mcp` binaries (with the embedded explorable-HTML engine) and the GitHub release that 0.5.3 missed.

## [0.5.3] - 2026-05-28

### Added

- `tla --present <manifest> --export-html <file> --explorable` embeds the wasm model-checking engine directly in the exported HTML, turning the offline walkthrough into a live state explorer (like interactive CLI mode, in the browser). The "Explore" tab steps through enabled actions from any state, shows live invariant results (`✓`/`✗` per spec invariant) at each state, and includes a REPL for evaluating TLA+ expressions against the current state. Requires building with `--features embed-wasm` (run `cargo make wasm` first to produce the `pkg/` artifacts that get inlined); the engine is base64-inlined and instantiated synchronously, so the file stays fully self-contained and works over `file://`. File-based `INSTANCE` modules are not available in-browser (single-file specs only).
- WASM bindings `explore_init` / `explore_next` / `explore_eval` / `explore_invariants` expose per-state stepping, successor enumeration, expression evaluation, and invariant checking to JS.

## [0.5.2] - 2026-05-27

### Fixed

- `action: <Name>` pinning in `replay_scenario` (and therefore `append_beat` / `validate_demo` beats and `--present` scenarios) could not match an action whose definition body is a top-level existential quantifier — `Op == \E x \in S: ...`. Those transitions were emitted unlabeled, so no `action: Op` line matched them and the user saw a misleading "no transition matches condition" even though the transition existed and was reachable. The action-name labeler descended through a top-level `\E` to name the inner body (which never equals the operator's stored body) before trying to match the whole `\E`; it now matches the whole existential against the operator definitions as a fallback. Affects the common `Action == \E p \in Procs: Step(p)` idiom. `available_actions` diagnostics and per-action stats now label these transitions by name as well.

## [0.5.1] - 2026-05-27

### Added

- Demo present mode. A demo manifest (JSON or TOML beside the spec) bundles named `variants` (spec + cfg / inline constant overrides) and ordered `beats`; each beat runs a `scenario` or a `replay` against one `variant` or several via `compare`, and checks `expect` / `expect_per_variant` assertions (`final:` / `all:` / `never:` / `step N:`).
  - `tla --present <manifest>` — guided TUI walkthrough: step beats, flip variants on compare beats, drop into live exploration mid-beat (`f`).
  - `tla --present <manifest> --validate` — non-interactive pass/fail report.
  - `tla --present <manifest> --export-md <file>` — generated, tested Markdown walkthrough.
  - `tla --present <manifest> --export-html <file>` — self-contained offline HTML walkthrough (side-by-side variant compare, step navigation, change highlighting, inline assertion results).
- Scenario `action: <Name>` / `action: <Name>; <predicate>` step kind pins a transition by action name, removing the need for a synthetic action-tag variable in specs.
- `tla-mcp`: `validate_demo`, `append_beat` (format-preserving — a `.toml` manifest stays TOML), `export_demo_doc`, and `export_demo_html` tools.
- `examples/time-integrity/` — a time-integrity alert state machine demo (3 variants, 4 beats; comparison beats + assertions), validated end to end.
- `default-run = "tla"` so plain `cargo run` resolves to the CLI.

### Fixed

- `tla-mcp`: `CheckStatsSummary.actions` and `.property_stats` were marked required in the generated output schema but omitted from responses whenever empty (any passing spec with no count properties), so strict MCP clients rejected every `check_spec` response with `-32602` "structured content does not match the tool's output schema". Both fields now carry `#[serde(default)]` and are correctly optional in the schema.
- `tla-mcp`: `append_beat` now persists a beat only when all its assertions pass; a beat that runs but fails an assertion returns status `failed` with the failing assertions and is not written.
- Scenario step predicates now resolve cfg constants (the matching env previously dropped them).
- `tla-mcp` exits on client disconnect, on SIGTERM/SIGINT, and on parent death (Linux `PR_SET_PDEATHSIG`) — prevents orphaned servers lingering for days.
- `scripts/install.sh` downloads to a temp file and atomically renames over the target, avoiding `ETXTBSY` and clobbering a running binary.

### Previously unreleased

v0.5.1 is the first published release since v0.4.3. The 0.4.4 and 0.4.5 changelog entries below were never tagged, so their changes ship here for the first time too (full detail in their sections):

- **0.4.5** — `tla-mcp` per-action transition counts (`CheckStatsSummary.actions`, sorted worst-first), `CheckSpecOutput.advisories` budget warnings (`max_depth > 100` / `max_states > 1_000_000`), and `docs/MCP_OBSERVABILITY.md`; `validate_spec`/`check_spec` tool descriptions now flag bounded vs. unbounded `Nat` / `Seq(T)` in `TypeOK` and document `max_seconds` as a soft bound checked between states.
- **0.4.4** — tuple-binding destructuring wherever a single-variable binder worked (quantifiers, set comprehensions, `CHOOSE`, function definitions; arbitrary nesting) and unbounded `CHOOSE x : x = e`; release and test builds no longer fail to link `tla-mcp` under `lto = "fat"` (lib `crate-type` narrowed to `rlib`, wasm adds `cdylib` on the command line).

## [0.4.5] - 2026-05-25

### Added

- `tla-mcp`: per-action transition counts in `CheckStatsSummary.actions`. Sorted descending by count so the worst offender is first — lets callers see at a glance which disjunct is driving state-space cost.
- `tla-mcp`: `CheckSpecOutput.advisories` array surfaces budget concerns before re-running. Currently warns when `max_depth > 100` or `max_states > 1_000_000`.
- `docs/MCP_OBSERVABILITY.md`: tracker doc for the broader observability roadmap (branching-factor estimator, progress streaming, symmetry static-check) — what's landed and what's deferred.

### Changed

- `tla-mcp` tool descriptions for `validate_spec` and `check_spec` now flag bounded vs. unbounded `Nat` / `Seq(T)` in `TypeOK`, document `max_seconds` as a soft bound checked between states (so it must be set well under the MCP client's timeout), and point at the rate × fanout projection workflow for stepping constants up safely.

## [0.4.4] - 2026-05-24

### Added

- Tuple-binding destructuring is now supported wherever a single-variable binder used to work. Each tuple binder is desugared at parse time to a synthetic name plus `LET` projections, so there are no AST or evaluator changes. Arbitrary nesting (`<<a, <<b, c>>>>`) works.
  - Quantifiers: `\E <<x, y>> \in S : P`, `\A <<x, y>> \in S : P`
  - Set comprehensions: `{<<x, y>> \in S : P}` and `{e : <<x, y>> \in S}`
  - `CHOOSE <<x, y>> \in S : P`
  - Function definitions: `[<<x, y>> \in S |-> e]`
- Unbounded `CHOOSE x : P` now handles the `x = e` pattern (returns `eval(e)` when `e` is independent of `x`) in addition to the existing `x \notin S` fresh-model-value pattern. General unbounded `P` still errors clearly. Unbounded `\E` / `\A` remain rejected — fundamentally not enumerable for explicit-state checking.

### Fixed

- `cargo test --release` and `cargo build --release --tests` no longer fail to link `tla-mcp`. The lib's `crate-type` was `["cdylib", "rlib"]`, which interacted with `lto = "fat"` to drop `JsonSchema` derive impls that the `#[tool_router]` macro in `tla-mcp` references. The lib now declares `crate-type = ["rlib"]` and wasm builds add `cdylib` on the command line via `cargo rustc --crate-type cdylib`. `Makefile.toml`, `.github/workflows/ci.yml`, and `.github/workflows/release.yml` were updated to match.
- `doctest = false` on the `[lib]` to avoid the related "same output filename" cargo warning when crate-types and tests are combined.
- Cleaned up three pre-existing clippy warnings in `src/checker.rs`, `src/export.rs`, and `tests/oracle.rs`.

## [0.4.3] - 2026-05-17

### Distribution

- `scripts/install.sh` — POSIX shell installer that detects platform (Linux x86_64, macOS x86_64, macOS arm64), fetches the appropriate prebuilt binaries from a GitHub release, **verifies SHA256 against the release's `SHA256SUMS` asset**, and drops them on the user's PATH. Flags: `--bin <tla|tla-mcp|both>`, `--version <tag>`, `--dir <path>`. Default install location is `$HOME/.local/bin`. Usable via `curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash`. Releases before v0.4.3 lack the `SHA256SUMS` asset and are rejected
- Release workflow now generates a `SHA256SUMS` asset (output of `sha256sum *` over the staged binary set) and attaches it to every GitHub release alongside the binaries
- `packaging/homebrew/tla-mcp.rb` — Homebrew formula installing both `tla` and `tla-mcp` from release binaries on macOS arm64, macOS x86_64, and Linux x86_64. Includes a `livecheck` block (`strategy :github_latest`) so `brew livecheck` and `brew bump-formula-pr` can detect new releases. Intended for a `homebrew-tla` tap repo (setup documented in `packaging/homebrew/README.md`); end users install with `brew install fabracht/tla/tla-mcp`
- README MCP "Install" section restructured to list all five paths (Homebrew, install script, cargo from crates.io, release binary download, `--path .` from a clone)

### Notes

- The formula in `packaging/homebrew/tla-mcp.rb` is a template pinned to the *previous* release (v0.4.2 here). On each new release, run `packaging/homebrew/README.md`'s SHA256-refresh recipe and commit the updated formula to the `homebrew-tla` tap repo. `brew bump-formula-pr` can automate the PR once the tap is established

## [0.4.2] - 2026-05-17

### Fixed

- Release workflow's `create-release` job no longer depends on `publish-npm`. The two are independent — a failed npm publish (e.g., expired or non-automation token) used to block the GitHub release page and binary asset uploads entirely. Now npm publish runs in parallel and its outcome is reported separately

## [0.4.1] - 2026-05-17

### Distribution

- Pre-built `tla-mcp` binaries are now produced by the release pipeline alongside `tla` for Linux x86_64, macOS x86_64, macOS arm64, and Windows x86_64. GitHub release assets are renamed to `tla-<platform>` and `tla-mcp-<platform>` to disambiguate
- README now advertises `cargo install tla-checker --bin tla-mcp` (no clone needed) as the primary install path for the MCP server, with the release-binary download and `--path .` workflows documented as alternatives

## [0.4.0] - 2026-05-17

### Added

- `tla-mcp` binary — Model Context Protocol server exposing the model checker as MCP tools for agentic clients (Claude Code, Cursor, etc.) over stdio transport. Four tools with versioned JSON schemas (`schema_version: "1"`):
  - `validate_spec` — parse + summary (vars, constants with resolved values, invariants, init/next presence)
  - `list_invariants` — detected invariant names (matches `Inv*`, `TypeOK*`, `NotSolved*`, plus cfg `INVARIANT` entries)
  - `check_spec` — full model checking with required `max_states` / `max_depth` / `max_seconds` budgets
  - `replay_scenario` — walk a spec step-by-step through a guided scenario (`step: <expression>` lines), returns per-step `StateSnapshot` + `changes`, or a failure with `available_actions` when no transition matches
- `tla_checker::mcp` module: schema types (`ValidateSpecOutput`, `CheckSpecOutput`, `StateSnapshot`, `TlaValue`, `StructuredError`), conversion helpers, and runner functions for direct library use
- `SpecSummary.constants: Vec<{ name, value }>` — `validate_spec` returns the spec's declared CONSTANTS with their resolved values (from cfg + input). Lets agents catch outlier constant values before launching a check that would have timed out
- `check_spec` requires a third budget `max_seconds: u64` (no default). The BFS loop and the liveness phase both check elapsed wall-clock time and return `status: "limit_reached"` with `limit: "max_seconds"` when the budget is hit. Previous behavior: long-running checks could exceed the MCP client's transport timeout, returning nothing structured
- `LimitKind::MaxSeconds` variant added to the schema; `CheckResult::MaxTimeExceeded(CheckStats)` variant added to the engine
- `check_spec` and `validate_spec` tool descriptions point at the validate-first workflow: call `validate_spec`, inspect `constants`, then `check_spec` with deliberate budgets
- `warnings` array on `validate_spec` and `list_invariants` responses — surfaces parser-tolerance warnings (silent operator-body skips that previously only printed to stderr) and unsupported temporal constructs (`<<A>>_v` diamond actions, `<>[]P` stable-eventually) dropped by the fairness extractor
- `parser::parse_with_warnings(input)` function returning `(Spec, Vec<Spanned<String>>)` for callers that want structured warnings; `parser::parse(input)` unchanged
- `CONSTRAINT` directive in cfg files is now honored — the checker prunes states where the constraint expression is false (matches TLC's `CONSTRAINT` semantics). Previously parsed but warned "not yet supported"
- `check_spec` MCP tool accepts `state_constraint: "<TLA+ expression>"` for inline state-space bounding without modifying the spec or cfg
- `CheckerConfig.state_constraints: Vec<Expr>` — the underlying field; populated either from cfg `CONSTRAINT` or library callers

### Fixed

- `SPECIFICATION` cfg directive now correctly extracts `WF_vars` / `SF_vars` / `<>` / `~>` from the referenced spec body. Previously, only definitions whose name ended in `Spec` were extracted by the parser; cfg `SPECIFICATION SomeOtherName` left temporal subexpressions in the init expression, where they crashed with "WF_vars cannot be evaluated as a state predicate"
- `collect_init` no longer pulls `WF_vars` / `SF_vars` / `Always` / `Eventually` / `LeadsTo` into the synthesized Init expression — these are temporal operators that must be routed to fairness/liveness, not to initial-state enumeration
- Temporal operator eval error messages now explain WHY the operator can't be evaluated and point at the correct cfg/spec structure
- **`<>P` (eventually) and `P ~> Q` (leads-to) liveness checks now use sub-SCC analysis** instead of treating the parent SCC as a single unit. Previous behavior: `check_leads_to` returned satisfied if `Q` held *anywhere* in the SCC, missing cases where the SCC contained sub-cycles staying in `!Q` forever. Now the check finds non-trivial sub-SCCs within the `!Q` (or `!P` for eventually) subset and reports a violation when one is reachable from a P-and-`!Q` state via `!Q` transitions. This catches classic starvation patterns (e.g., a reader/writer lock where the writer's `~>` is violated by an infinite reader-cycle within a larger SCC that happens to include a writer-active state)
- Leads-to violation reports now include the actual problematic sub-SCC as the cycle, not the full parent SCC. Previously the reported cycle would contain irrelevant `Q`-holding states
- **Leads-to violation now reports the sub-SCC the P-state actually reaches**, not just the first non-trivial sub-SCC in Tarjan order. When multiple non-trivial `!Q` sub-SCCs exist, the previous logic could report a cycle that is unreachable from any P-state while a real violation existed elsewhere. The reported cycle is now correct
- `max_seconds` budget is now enforced during the liveness phase, not just BFS. Previously, specs where BFS finished within budget but the liveness phase (forward-edge reconstruction + Tarjan + sub-SCC analysis) ran long could exceed the MCP client's transport timeout. Now the check fires at the top of the per-state edge loop and between liveness property checks
- `state_constraint` parse errors now include the source span pointing into the user's constraint expression. Previously the span was dropped
- `extract_fairness_and_liveness` now warns when it encounters `<<A>>_v` (diamond action) or `<>[]P` (stable-eventually) — both are silently dropped today but the warning surfaces the cfg-debug mismatch instead of leaving the user wondering why fairness wasn't applied
- `state_passes_constraints` no longer clones `base_env` on every state and every transition — the env is hoisted out of both loops and reused, matching the pattern used elsewhere in the BFS loop

### Performance

- Liveness checking now reuses forward edges collected during BFS exploration instead of recomputing successors via a second `next_states` pass over every reachable state. For specs with expensive `Next` evaluation this halves the per-state evaluation cost when `check_liveness` is enabled. Closes #36 (#38)

### Notes

- `check_spec` inputs `allow_deadlock` and `check_liveness` are `Option<bool>`: omit to defer to cfg directives (`CHECK_DEADLOCK`, `PROPERTY`), pass explicitly to override. The `symmetry` field appends to cfg `SYMMETRY` constants rather than replacing them
- README section on MCP mid-session reload: clients spawn server processes at startup; rebuilding doesn't hot-reload — restart the client (or open a new session) to pick up changes
- Constraint expressions are evaluated against unprimed variables (state predicates). They run at both initial-state enumeration and successor expansion, before symmetry canonicalization. `ACTION_CONSTRAINT` (transition predicate) remains unsupported and still warns
- `Spec::extract_fairness_and_liveness(&mut self, &Expr)` is now a public method on `Spec`, callable from both the parser (auto-extraction on `*Spec` definition names) and `apply_config` (when `SPECIFICATION` resolves to a non-`*Spec` name)
- `scc::compute_sccs_in_subset(graph, allowed: &HashSet<usize>)` — new public function running Tarjan over a filtered node set, used by the liveness checks to find sub-SCCs within `!P` / `!Q` partitions
- The liveness sub-SCC analysis is sound (any reported violation is real) and complete when the parent SCC is fair, but does not check fairness on the sub-SCC itself — a !Q sub-cycle that happens to be unfair will still be reported. In practice rare for typical specs; flagged here for future tightening
- `check_leads_to` and `check_eventually` now return `Result<Option<Vec<usize>>>` (Some = sub-SCC states forming the violating cycle, None = property satisfied), enabling accurate cycle reporting
- `Spec::extract_fairness_and_liveness` now returns `Vec<String>` of warnings (empty when nothing unexpected). Callers in the parser and `apply_config` collect and surface these
- BFS now collects forward edges in `all_edges` whenever liveness checking is enabled, not only when DOT export is requested. This adds memory proportional to total transitions (one `(usize, Option<Arc<str>>)` per edge) during the BFS phase, in exchange for skipping the duplicate `next_states` pass during liveness. Specs that are state-count-bounded but memory-tight may need to budget for the extra edge storage
- `tla-mcp` binary is shipped as source in this release (`cargo install --bin tla-mcp`); pre-built binaries for the MCP server are not yet produced by the release pipeline

## [0.3.11] - 2026-05-02

### Fixed

- Parser auto-detection for `Init` / `Next` / invariant names no longer misclassifies parameterized helpers. Operators like `InvokeAction(p)`, `InitNode(k)`, or `NextStep(n)` were being treated as the spec's Init/Next or as invariants and evaluated with their parameters unbound, causing `undefined variable` errors at state 0. Fix gates all three classifications on `params.is_none()` (#35)

### Added

- `test_cases/should_pass/FRList.tla` — Fomitchev–Ruppert lock-free linked list, structural correctness (paper Inv 1–5 plus three derived invariants), with auto-loaded `FRList.cfg` and oracle test
- `test_cases/should_pass/FRListLin.tla` — adds a per-process operation layer with an abstract dictionary, checks the refinement invariant `dict = RegularKeys` plus per-op response validity, with auto-loaded `FRListLin.cfg` and oracle test
- `test_cases/should_pass/parameterized_inv_prefix.tla` — regression test locking in the auto-detection fix

## [0.3.10] - 2026-04-19

### Fixed

- `~` (negation) operator precedence: `~state \in S` now correctly parses as `~(state \in S)` instead of `(~state) \in S` (#33)

## [0.3.9] - 2026-04-08

### Added

- CI jobs `clippy-wasm`, `test-wasm`, and `build-wasm32` exercising the `wasm` feature on host and the real `wasm32-unknown-unknown` target
- Host-runnable tests covering every `CheckResult` and `PrepareSpecError` variant exposed through the wasm bindings

### Changed

- Internal consolidation of `src/wasm.rs`: all four `wasm_bindgen` entry points now flow through a single `check_internal` helper, with shared `WasmCheckResult` constructors for the `CheckResult → JSON` mapping (no public API change)
- `prepare_spec` and `CheckerConfig::spec_path` are now compiled on `wasm32-unknown-unknown`, fixing the previously broken target build

## [0.3.8] - 2026-04-07

### Fixed

- Variant names in wasm.rs (`CheckResult` arm names matched against wrong string literals)
- Clippy `missing_const_for_thread_local` warning on `RNG` thread-local

## [0.3.7] - 2026-04-03

### Fixed

- `..` (range) operator not recognized in recursive function domains (`f[i \in 1..N]`) and CHOOSE domains (`CHOOSE x \in 1..N : P`)
- INSTANCE/EXTENDS resolution in interactive mode
- Finding initial states through static instance references (e.g., `Init == MyInstance!Init /\ ...`)

### Added

- Practical TLA+ user guide with paired specs for writing actions patterns

## [0.3.6] - 2026-03-23

### Fixed

- IF expressions with bulleted conjunction lists as conditions (`IF /\ cond1 /\ cond2 THEN`)
- IF conditions with multi-line inline conjunctions where `/\` is outdented relative to the first operand
- Leading `/\` in IF THEN/ELSE branches (e.g., `THEN /\ expr1 /\ expr2`)
- Nested EXCEPT updates through records inside functions (`[f EXCEPT ![key].field = val]`)

## [0.3.5] - 2026-03-22

### Fixed

- `contains_prime_ref` infinite recursion when analyzing `RECURSIVE` operator bodies, causing the checker to hang on any spec using recursive operators inside Next actions

## [0.3.4] - 2026-03-08

### Fixed

- `SPECIFICATION` cfg directive extracting only the first init conjunct, producing 0 initial states for multi-variable specs

## [0.3.3] - 2026-02-25

### Added

- WASM build pipeline with clean, `package.json` generation, and npm packaging
- `wasm-publish` task for npm publishing

### Fixed

- Inline `\/` operators within bulleted disjunction lists (e.g., `\/ A \/ B \/ C` on one line)
- `SPECIFICATION` cfg directive failing to find definitions ending with `Spec`
- Nested bulleted `\/` lists inside parentheses now use `parse_and_item` for correct inline handling

## [0.3.2] - 2026-02-16

### Fixed

- `(unnamed)` action labels in counterexample traces

### Added

- `counterexample_actions_alignment` test case
- `.cfg` files for specs that need constants

## [0.3.1] - 2026-02-14

### Added

- `--dot-mode` flag with four DOT export modes: `clean` (default), `full`, `trace`, `choices`
- `DotExport` context struct for cleaner `export_dot` API
- WASM `dot_mode` option in `check_spec_with_options`

### Changed

- Default DOT export changed from full (all edges) to clean (no self-loops, parallel edges merged)
- `export_dot` now takes a `DotExport` struct instead of individual parameters

## [0.3.0] - 2026-02-13

### Added

- TLC-compatible `.cfg` file parser with auto-discovery (`Spec.cfg` next to `Spec.tla`)
- Supported directives: INIT, NEXT, SPECIFICATION, CONSTANT(S), INVARIANT(S), PROPERTY/PROPERTIES, SYMMETRY, CHECK_DEADLOCK
- WASM `check_spec_with_options` API with unified options object
- WASM `check_spec_with_cfg` API for cfg file support
- WASM unit tests
- Bench profile (`panic = "unwind"`, `strip = false`)

### Changed

- Batch candidate inference across all variables in a single AST walk
- Replaced `Env` BTreeMap with Vec-backed struct (~15% speedup on model checking)
- Extracted `substitution.rs` from `modules.rs` for expression substitution logic
- Gated `ratatui`/`crossterm` dependencies for non-WASM targets only
- `CheckResult::NextError` and `InvariantError` now carry DOT graph data
- `do_export` refactored to return `Option<String>` for WASM compatibility

### Fixed

- WASM constant/cfg precedence: JSON constants now correctly override cfg constants
- WASM `allow_deadlock` flag now properly propagated to `apply_config`
- `substitute_expr` now recurses into TLC builtins and Bag operations
- `Env::remove` preserves insertion order (changed from `swap_remove` to `remove`)
- `split_top_level` handles escaped quotes and brace depth correctly

## [0.2.0] - 2026-02-05

### Added

- Parameterized INSTANCE declarations (`Alias(p) == INSTANCE M WITH ...`)
- Qualified calls to instance operators (`Alias!Op(args)`, `Alias(v)!Op(args)`)
- Library module support (modules without Init/Next can be used as INSTANCE targets)
- Stdlib modules (Naturals, Sequences, TLC, etc.) work with `LOCAL INSTANCE`
- `UNCHANGED<<vars>>` now expands tuple-valued definitions (e.g., `vars == <<x, y>>`)

## [0.1.1] - 2026-02-05

### Fixed

- Eliminated all production `unwrap`/`expect`/`panic` calls in checker, SCC, interactive mode, module registry, and renderer
- Fixed O(N^4) next-state enumeration for specs with top-level `\E` (existential quantifier) — mutex.tla with 78 processes went from ~2 minutes to under 1 second

### Changed

- `next_states_impl` now resolves zero-argument definition references before dispatching to `expand_and_enumerate` or `enumerate_next`

## [0.1.0] - 2026-02-04

Initial public release.

### Features

- Full TLA+ model checker with BFS state exploration
- Recursive descent parser for TLA+ specifications
- Interactive TUI mode (`--interactive`) with state exploration, expand/collapse for grouped changes
- Counterexample replay mode (`--replay`)
- Symmetry reduction (`--symmetry`)
- Liveness checking with fairness constraints and SCC algorithm (`--check-liveness`)
- Scenario exploration (`--scenario`)
- Parameter sweeps (`--sweep`)
- Property counting with depth-stratified breakdowns (`--count-satisfying`)
- Continue past violations to collect all counterexamples (`--continue`)
- DOT graph export (`--export-dot`)
- JSON output (`--json`)
- Counterexample trace export (`--trace-json`, `--save-counterexample`)
- WASM target support

### Standard Library Modules

- Naturals, Integers, Reals
- Sequences (including `SortSeq`, `SelectSeq`, `Permutations`)
- FiniteSets
- Bags
- Bits (bitwise operators)
- TLC (PrintT, ToString, RandomElement, TLCGet, TLCSet, Assert)

### Performance

- Vec-based state representation (replacing BTreeMap)
- Env caching and primed variable name caching in BFS loop
- Disjunct decomposition for next-state evaluation
- Release profile with LTO, single codegen unit, and symbol stripping (1.3M binary)
