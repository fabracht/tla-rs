# Changelog

## [Unreleased]

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
