# Changelog

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
