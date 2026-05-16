# Changelog

## [Unreleased]

### Added

- `CONSTRAINT` directive in cfg files is now honored — the checker prunes states where the constraint expression is false (matches TLC's `CONSTRAINT` semantics). Previously parsed but warned "not yet supported"
- `check_spec` MCP tool accepts `state_constraint: "<TLA+ expression>"` for inline state-space bounding without modifying the spec or cfg
- `CheckerConfig.state_constraints: Vec<Expr>` — the underlying field; populated either from cfg `CONSTRAINT` or library callers

### Fixed

- `SPECIFICATION` cfg directive now correctly extracts `WF_vars` / `SF_vars` / `<>` / `~>` from the referenced spec body. Previously, only definitions whose name ended in `Spec` were extracted by the parser; cfg `SPECIFICATION SomeOtherName` left temporal subexpressions in the init expression, where they crashed with "WF_vars cannot be evaluated as a state predicate"
- `collect_init` no longer pulls `WF_vars` / `SF_vars` / `Always` / `Eventually` / `LeadsTo` into the synthesized Init expression — these are temporal operators that must be routed to fairness/liveness, not to initial-state enumeration
- Temporal operator eval error messages now explain WHY the operator can't be evaluated and point at the correct cfg/spec structure
- **`<>P` (eventually) and `P ~> Q` (leads-to) liveness checks now use sub-SCC analysis** instead of treating the parent SCC as a single unit. Previous behavior: `check_leads_to` returned satisfied if `Q` held *anywhere* in the SCC, missing cases where the SCC contained sub-cycles staying in `!Q` forever. Now the check finds non-trivial sub-SCCs within the `!Q` (or `!P` for eventually) subset and reports a violation when one is reachable from a P-and-`!Q` state via `!Q` transitions. This catches classic starvation patterns (e.g., a reader/writer lock where the writer's `~>` is violated by an infinite reader-cycle within a larger SCC that happens to include a writer-active state)
- Leads-to violation reports now include the actual problematic sub-SCC as the cycle, not the full parent SCC. Previously the reported cycle would contain irrelevant `Q`-holding states

### Notes

- Constraint expressions are evaluated against unprimed variables (state predicates). They run at both initial-state enumeration and successor expansion, before symmetry canonicalization. `ACTION_CONSTRAINT` (transition predicate) remains unsupported and still warns
- `Spec::extract_fairness_and_liveness(&mut self, &Expr)` is now a public method on `Spec`, callable from both the parser (auto-extraction on `*Spec` definition names) and `apply_config` (when `SPECIFICATION` resolves to a non-`*Spec` name)
- `scc::compute_sccs_in_subset(graph, allowed: &HashSet<usize>)` — new public function running Tarjan over a filtered node set, used by the liveness checks to find sub-SCCs within `!P` / `!Q` partitions
- The liveness sub-SCC analysis is sound (any reported violation is real) and complete when the parent SCC is fair, but does not check fairness on the sub-SCC itself — a !Q sub-cycle that happens to be unfair will still be reported. In practice rare for typical specs; flagged here for future tightening
- `check_leads_to` and `check_eventually` now return `Result<Option<Vec<usize>>>` (Some = sub-SCC states forming the violating cycle, None = property satisfied), enabling accurate cycle reporting

## [0.4.0] - 2026-05-14

### Added

- `tla-mcp` binary — Model Context Protocol server exposing the model checker as MCP tools for agentic clients (Claude Code, Cursor, etc.) over stdio transport
- Three MCP tools with versioned JSON schemas: `validate_spec` (parse + summary), `list_invariants` (introspection), `check_spec` (full check with required `max_states` / `max_depth` budgets)
- `tla_checker::mcp` module: schema types (`ValidateSpecOutput`, `CheckSpecOutput`, `StateSnapshot`, `TlaValue`, `StructuredError`), conversion helpers, and runner functions for direct library use

### Notes

- `check_spec` inputs `allow_deadlock` and `check_liveness` are `Option<bool>`: omit to defer to cfg directives (`CHECK_DEADLOCK`, `PROPERTY`), pass explicitly to override. The `symmetry` field appends to cfg `SYMMETRY` constants rather than replacing them.

### Added (follow-ups)

- `replay_scenario` MCP tool — walks a spec through a guided scenario (`step: <expression>` lines) and returns per-step `StateSnapshot` + `changes`, or a failure with `available_actions` when no transition matches a step
- `warnings` array on `validate_spec` and `list_invariants` responses — surfaces parser-tolerance warnings (silent operator-body skips) that previously only printed to stderr
- README section on MCP mid-session reload (clients spawn server processes at startup; rebuilding doesn't hot-reload)
- New `parser::parse_with_warnings(input)` function returning `(Spec, Vec<Spanned<String>>)` for callers that want structured warnings; `parser::parse(input)` unchanged

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
