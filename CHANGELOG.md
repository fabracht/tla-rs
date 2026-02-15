# Changelog

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
