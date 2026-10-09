# tla-checker Architecture

This document describes the internals of tla-checker (tla-rs), a TLA+ model checker written in Rust. For user-facing documentation see [README.md](README.md), [CLI_GUIDE.md](CLI_GUIDE.md) (every flag and cfg directive), [MCP.md](MCP.md) (the MCP server), [WASM.md](WASM.md) (the WebAssembly bindings) and [TLA_SUPPORT.md](TLA_SUPPORT.md) (language coverage).

## Overview

tla-checker is an explicit-state model checker. It parses a TLA+ module, computes every reachable state by breadth-first search, checks invariants and the safety parts of `PROPERTY` formulas on each state and transition, and, when liveness checking is enabled, searches the explored state graph for a fair behavior that violates a temporal property.

## Crate Structure

The package `tla-checker` builds one library and two binaries:

| Target | Path | Purpose |
|--------|------|---------|
| library `tla_checker` (`crate-type = ["rlib"]`) | `src/lib.rs` | Parser, evaluator, checker, MCP runner, demo tooling |
| binary `tla` (default) | `src/main.rs` | Command-line model checker |
| binary `tla-mcp` | `src/bin/tla_mcp.rs` | MCP server over stdio |

The WebAssembly build compiles the library as a `cdylib` for `wasm32-unknown-unknown` with the `wasm` feature (`cargo make wasm`, see `Makefile.toml`), then runs `wasm-bindgen --target web` into `pkg/`.

Cargo features:

| Feature | Effect |
|---------|--------|
| `wasm` | Enables `src/wasm.rs` (`wasm-bindgen` + `serde`) |
| `embed-wasm` | Embeds `pkg/tla_checker_bg.wasm` and `pkg/tla_checker.js` into the binary so `--explorable` HTML export works (`base64`) |
| `profiling` | Collects init/next-state timing in the evaluator and prints it after a check |
| `dhat` | Installs the `dhat` heap profiler as the global allocator in `tla` |

Modules that need a filesystem, a terminal or tokio (`demo`, `interactive`, `load`, `mcp`, `modules`) are compiled only when not targeting `wasm32`.

Release builds use `lto = "fat"`, `codegen-units = 1`, `strip = true`, `panic = "abort"`. A `profiling` profile inherits release with debug info and without LTO.

## Module Map

### Root modules (`src/`)

| File | Responsibility |
|------|----------------|
| `lib.rs` | Module declarations and re-exports |
| `main.rs` | `tla` CLI: argument parsing, mode dispatch, human/JSON output, exit codes |
| `bin/tla_mcp.rs` | `tla-mcp` binary: `rmcp` tool router over stdio, delegating to `mcp::runner` |
| `ast.rs` | Core types (`Value`, `Expr`, `Env`, `State`, `Spec`, …), `PROPERTY` classification (`classify_property`, `Normalizer`), temporal helpers (`collect_temporal`, `leads_to_form`, `without_fairness`) |
| `lexer.rs` | Tokenizer |
| `parser/` | Recursive-descent parser producing a `Spec` |
| `eval/` | Expression evaluation, initial-state and successor generation, `ENABLED` |
| `checker.rs` | `prepare_spec` (module loading, constants, ASSUME), BFS, safety checks, liveness orchestration, symmetry expansion for liveness, trace formatting, JSON result encoding |
| `config.rs` | TLC `.cfg` parser (`parse_cfg`) and `apply_config`, constant value parser (`parse_constant_value`) |
| `load.rs` | `prepare_from_path`: read + parse + EXTENDS merge + cfg discovery/application, used by the demo tooling, the presenter and integration tests |
| `modules.rs` | `ModuleRegistry` (loads `<Name>.tla` next to the spec, with cycle detection), `resolve_instances`, `merge_extended_declarations` |
| `substitution.rs` | `substitute_expr` (capture-avoiding, renames bound variables via `fresh_name`) and `apply_substitutions` for `INSTANCE ... WITH` |
| `stdlib.rs` | Built-in modules: `BOOLEAN`, `STRING`, `Nat`, `Int`; recognizes `Naturals`, `Integers`, `Sequences`, `FiniteSets`, `TLC`, `Bags`, `Bits` as standard modules (their operators are `Expr` variants handled by the parser and evaluator) |
| `level.rs` | `LevelAnalysis`: constant/state/action/temporal level of an expression, as SANY (`exact`) and as TLC's coarser bound (`bound`) |
| `liveness.rs` | `FairnessTable` (WF/SF enabledness and occurrence, Emerson–Lei `fair_components`, `witness_cycle`) and the legacy property-shape checks (`find_violation`) |
| `ltl.rs` | `ltl::Builder`: TLA+ temporal formula → negation-normal-form `Ltl` over an `AtomTable` |
| `tableau.rs` | Manna–Pnueli tableau construction (`tableau::build`) |
| `ltl_check.rs` | State × tableau product and the search for a fair accepting component (`compile`, `find_behavior`) |
| `scc.rs` | Iterative Tarjan SCC over any `LivenessGraph` |
| `graph.rs` | `StateGraph` (states, edges with optional renamed target, parent pointers) and the `LivenessGraph` trait |
| `symmetry.rs` | `SymmetryConfig`: canonicalization, the permutation group (`group`), `permute` |
| `refinement.rs` | `--check-refinement`: checks `Spec => Alias!Spec` for a non-parameterized `INSTANCE` alias |
| `scenario.rs` | Scenario parsing (`step:` / `action:` lines) and replay against the spec |
| `export.rs` | Graphviz DOT export with modes `full`, `trace`, `clean` (default), `choices` |
| `trace_io.rs` | `Value`/`State` ↔ `serde_json::Value`, used for replay files and the WASM explorer |
| `intern.rs` | Thread-local interning of names and primed names (`primed_name`) |
| `diagnostic.rs` | `Diagnostic` (error/warning with span, label, note, help), plain and colored rendering, "did you mean" suggestions |
| `source.rs`, `span.rs` | Source text with line index; byte-offset `Span` and `Spanned<T>` |
| `wasm.rs` | `wasm-bindgen` bindings (feature `wasm`) |

### Parser (`src/parser/`)

| File | Responsibility |
|------|----------------|
| `mod.rs` | Entry points `parse`, `parse_with_warnings`, `parse_expr` |
| `lexing.rs` | `Parser` struct over the token stream, lookahead, name-detection rules for Init/Next/invariants |
| `spec.rs` | Module-level units: `MODULE`, `EXTENDS`, `VARIABLES`, `CONSTANTS`, `ASSUME`, definitions, `INSTANCE`, proofs (skipped) |
| `expr.rs` | Expression precedence chain, aligned `/\` / `\/` bullet lists |
| `primary.rs` | Primary expressions: literals, sets, functions, records, tuples, quantifiers, `LET`, `IF`, `CASE`, `UNCHANGED`, etc. |
| `error.rs` | `ParseError` with span, expected/found and help text |

### Evaluator (`src/eval/`)

| File | Responsibility |
|------|----------------|
| `mod.rs` | Public API re-exports; `Definitions`, `ParameterizedInstance` |
| `core.rs` | `eval`: the main expression dispatch, wrapped in `stacker::maybe_grow` |
| `walk.rs` | Default successor/initial-state engine: continuation-passing walk of `Init`/`Next` (a port of TLC's `getNextStates`); also the `ENABLED` walk |
| `enumerate.rs`, `candidates.rs`, `init.rs` | Legacy candidate-inference engine (selected with `TLA_ENGINE=inference`), dispatch to the walker, guard extraction for the interactive mode |
| `state.rs` | `next_states`, `next_states_with_guards`, `is_action_enabled`, `is_angle_action_enabled`, `angle_action_enabled_in` |
| `context.rs` | `eval_with_context` (evaluation with state variables in scope), `eval_with_instances` |
| `recursive.rs` | Recursive function definitions, memoized through a thread-local stack of active functions |
| `global_state.rs` | Thread-locals: resolved and parameterized instances, TLCGet/TLCSet state, checker statistics, RNG seed, state variables in scope, `SYMBOLIC_INTEGERS`, enumeration caps |
| `combinatorics.rs` | Permutations, k-combinations, sub-bag enumeration, `SUBSET` with cardinality constraints |
| `helpers.rs` | Typed eval helpers, symbolic set membership (`in_set_symbolic`), nested function update |
| `ast_utils.rs` | AST queries (prime references, state references, action-name inference, disjunct collection) |
| `diagnostics.rs` | `explain_invariant_failure` |
| `error.rs` | `EvalError` |

### Interactive (`src/interactive/`)

| File | Responsibility |
|------|----------------|
| `mod.rs` | `run_interactive`, `run_interactive_replay` |
| `present.rs` | `run_presentation`: TUI presenter for demo manifests (`--present`) |
| `state.rs` | `ExplorerState`: current state, history, enabled actions, REPL input |
| `input.rs` | Key handling and app loops for explore and replay |
| `render.rs` | ratatui layout and rendering |
| `repl.rs` | Expression REPL and hypothesis testing against the current state |
| `serialize.rs` | Re-exports the `trace_io` JSON state conversion |

### Demo tooling (`src/demo/`)

| File | Responsibility |
|------|----------------|
| `manifest.rs` | `Manifest` (JSON or TOML): named `variants` (spec, cfg, constants) and ordered `beats` |
| `beat.rs` | `run_beat`: replays a beat's scenario or replay file per variant and evaluates its `expect` assertions |
| `doc.rs` | `render_doc`: Markdown walkthrough |
| `html.rs` | `render_html` (self-contained walkthrough, `templates/walkthrough.html`) and `render_explorable` (embeds the wasm engine, `templates/explorable.html`; requires `embed-wasm`) |

### MCP (`src/mcp/`)

| File | Responsibility |
|------|----------------|
| `mod.rs` | `SCHEMA_VERSION` (currently `"2"`) |
| `schema.rs` | `serde`/`schemars` input and output types for every tool |
| `runner.rs` | Synchronous tool implementations on top of the library |

## Data Flow

```
.tla ──▶ lexer ──▶ parser ──▶ Spec ──▶ merge_extended_declarations ──▶ apply_config (.cfg)
                                                                              │
                                                                              ▼
                       prepare_spec: stdlib, EXTENDS/INSTANCE modules, constants, ASSUME
                                                                              │
                                                                              ▼
            BFS: init_states ─▶ invariants / PROPERTY parts ─▶ next_states ─▶ dedup
                                                                              │
                                                     (liveness enabled)       ▼
                         StateGraph ─▶ FairnessTable ─▶ tableau product search or legacy checks
```

1. **Parse.** `parser::parse_with_warnings` builds a `Spec`. A definition whose body fails to parse is kept as `Expr::Unparsed` and reported as a warning; using it fails with the parse error.
2. **EXTENDS merge.** `modules::merge_extended_declarations` adds the variables, constants and definitions of extended user modules (transitively; the extending module's definitions win).
3. **Configuration.** The cfg (explicit `--config`, else `<Spec>.cfg` next to the spec) is parsed and applied. CLI constants override cfg constants.
4. **Preparation.** `checker::prepare_spec` loads built-in modules, loads and resolves `EXTENDS`/`INSTANCE` modules from the spec's directory, evaluates cfg `Name <- Def` substitutions, reports missing constants, and evaluates `ASSUME`.
5. **Search.** `checker::check` runs the BFS and, if needed, liveness checking, returning a `CheckResult`.

## Binary & CLI

`tla <spec.tla> [options]` has no subcommands; a first argument such as `check`, `run`, `verify`, `parse`, `lint` or `test` is rejected with a usage hint. The full flag list is in [CLI_GUIDE.md](CLI_GUIDE.md) and `tla --help`.

`main` parses arguments into a `CheckerConfig` plus mode flags, then dispatches in this order:

1. `--version` / `--help` print and exit.
2. `--present FILE` runs a demo manifest: with `--export-html` (optionally `--explorable`) or `--export-md` it writes a walkthrough, with `--validate` it prints a pass/fail report, otherwise it opens the TUI presenter. No spec argument is needed.
3. Otherwise the spec is parsed, extended modules merged and the cfg applied.
4. `--list-invariants` and `--validate` report on the prepared spec and exit.
5. `--scenario` replays a scenario; `--replay` and `--interactive` open the TUI.
6. `--sweep NAME=V1;V2;...` runs one check per value and prints a comparison table.
7. Otherwise one `check` runs, printed as text or, with `--json`, as `check_result_to_json`.

Environment variable `TLA_ENGINE=inference` selects the legacy candidate-inference successor engine instead of the walker.

Exit codes: `0` when the check completes without violations (also when `--quick` stops at its state limit, and for successful validate/list/scenario/replay/present runs); `1` for any violation, error, deadlock, or a state/depth limit reached outside quick mode.

## Core Types (`ast.rs`)

### Value

```rust
pub enum Value {
    Bool(bool),
    Int(i64),
    Str(Arc<str>),
    Model(Arc<str>),
    Set(Arc<BTreeSet<Value>>),
    Fn(Arc<BTreeMap<Value, Value>>),
    Record(Arc<BTreeMap<Arc<str>, Value>>),
    Tuple(Arc<Vec<Value>>),
    IntSet(IntDomain),
}
```

- Function values are canonicalized on construction: a map whose domain is `1..n` (including the empty map) becomes `Tuple`, one whose non-empty domain is all strings becomes `Record`, anything else stays `Fn`. A record, a sequence and the same function written with `:>`/`@@` are therefore one value, and the derived `Eq`/`Ord`/`Hash` used for deduplication are correct by construction.
- `Model` values are distinct from strings: model value `n1` never equals `"n1"`.
- `IntSet(IntDomain)` is an infinite set decided by membership only: `STRING` always, and `Nat`/`Int` under symbolic integers. Enumerating it is an error.
- Collections are behind `Arc`, so cloning a value is cheap.

### Expr

`Expr` has about 110 variants. Groups:

- Literals and names: `Lit`, `Var`, `Prime`, `OldValue` (`@`), `Unparsed` (a definition that did not parse).
- Logic, comparison and arithmetic: `And`, `Or`, `Not`, `Implies`, `Equiv`, `Eq`, `Neq`, `Lt`/`Le`/`Gt`/`Ge`, `In`, `NotIn`, `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Exp`, `Neg`, `BitwiseAnd`.
- Sets: `SetEnum`, `SetRange`, `SetFilter`, `SetMap`, `Union`, `Intersect`, `SetMinus`, `Cartesian`, `Subset`, `ProperSubset`, `Powerset`, `BigUnion`, `Cardinality`, `IsFiniteSet`.
- Binders: `Exists`, `Forall`, `Choose`, `ChooseUnbounded`, `Let`, `Lambda`.
- Functions, records, tuples: `FnApp`, `FnDef`, `FnCall` (operator application), `FnMerge` (`@@`), `SingleFn` (`:>`), `Except`, `Domain`, `FunctionSet`, `RecordLit`, `RecordSet`, `RecordAccess`, `TupleLit`, `TupleAccess`, `CustomOp` (predefined backslash infix operators such as `\prec` or `\oplus`, including user definitions of them; a user definition with a symbol name such as `**` does not parse, [#186](https://github.com/fabracht/tla-rs/issues/186)).
- Sequences, Bags and TLC module operators (`Len`, `Append`, `SubSeq`, `SelectSeq`, `SeqSet`, `BagAdd`, `SubBag`, …, `Print`, `Assert`, `Permutations`, `SortSeq`, `RandomElement`, `TLCGet`, `TLCSet`, `TLCEval`, `Any`, …) are dedicated variants.
- Relations: `TransitiveClosure` (`^+`), `ReflexiveTransitiveClosure` (`^*`), `ActionCompose` (`\cdot`).
- Control: `If`, `Case`, `Unchanged`, `LabeledAction`.
- Temporal: `Always`, `Eventually`, `LeadsTo`, `WeakFairness`, `StrongFairness`, `BoxAction` (`[A]_v`), `DiamondAction` (`<<A>>_v`), `EnabledOp`.
- Modules: `QualifiedCall` (`I!Op(args)`, including parameterized `I(x)!Op`).

### Env and State

```rust
pub struct Env { entries: Vec<(Arc<str>, Value)> }
pub struct State { pub values: Vec<Value> }
```

`Env` is a small association list; lookups compare `Arc` pointers first and fall back to string comparison, which is why names are interned (`intern.rs`). `State` holds one value per entry of `spec.vars`, in order.

### Spec

`Spec` holds the module's `vars`, `constants`, `extends`, `definitions` (`DefinitionMap = BTreeMap<name, (params, Arc<Expr>)>`), `assumes`, `instances` (`InstanceDecl`: alias, params, module, `WITH` substitutions), `init` and `next` (both `Option<Expr>`, so library modules parse), `invariants` with parallel `invariant_names`, `fairness`, `quantified_fairness`, `liveness_properties` (`LivenessProperty { name, formula, from_specification }`), `safety_properties` (`SafetyProperty::Init` / `SafetyProperty::Action`), `temporal_assumptions` (non-fairness conjuncts of the cfg `SPECIFICATION`) and `constant_substitutions` (cfg `Name <- Def`).

Other types in `ast.rs`: `Transition { state, action }`, `FairnessConstraint::{Weak, Strong}(subscript, action)`, `PropertyPart`, `Classification`, and the guard/diagnostic records used by the interactive mode and invariant explanations (`GuardEval`, `TransitionWithGuards`, `VarChange`, `SubExprEval`, `InvariantViolationInfo`).

## Lexer

`lexer.rs` turns source into tokens with spans. It handles decimal, `\b` binary, `\o` octal and `\h` hexadecimal integers, string escapes, line (`\*`) and block (`(* *)`) comments, separator lines (`----`, `====`), ASCII operators and their word-form aliases (`\land`, `\lor`, `\lnot`, …), and the TLA+ keywords.

## Parser

A recursive-descent parser. Expression precedence, lowest to highest (`parser/expr.rs`):

1. `=>`, `<=>`, `~>`
2. `\/` (aligned bullet lists and labels `l :: e`)
3. `/\` (aligned bullet lists)
4. comparisons: `=`, `#`, `<`, `<=`, `>`, `>=`, `\in`, `\notin`, `\subseteq`, …
5. `@@`
6. `:>`
7. `..`
8. additive: `+`, `-`, `\union`, `\intersect`, `\`, `\times`, `\o`, bag `(+)` / `(-)`, backslash infix operators (`CustomOp`)
9. multiplicative: `*`, `/`, `\div`, `%`, `&`
10. `^`
11. prefix: `~`, `-`, `DOMAIN`, `SUBSET`, `UNION`, `ENABLED`, `[]`, `<>`, …
12. postfix: `'`, `[...]`, `.field`, `^+`, `^*`, `!`

Spec-level detection in `parser/spec.rs` and `parser/lexing.rs`:

- A zero-parameter definition named `Init` or `Next`, or a module prefix plus that name (an all-uppercase prefix such as `TPInit`, or one ending in `_` such as `M_Next`), becomes `spec.init` / `spec.next`.
- A zero-parameter definition whose name starts with `Inv`, `TypeOK` or `NotSolved`, or is a module prefix followed by `Inv`/`TypeOK`, becomes an invariant. A cfg `INVARIANT` section replaces this list.
- A zero-parameter definition whose name ends in `Spec` has its `WF`/`SF` conjuncts extracted into `fairness`/`quantified_fairness` and its other temporal conjuncts into `liveness_properties` (marked `from_specification`). A cfg that defines the behavior (`SPECIFICATION`, `INIT` or `NEXT`) clears these.
- Proof steps (`THEOREM`, `LEMMA`, `BY`, `QED`, …) are skipped.

## Evaluator

`eval(expr, env, defs) -> Result<Value, EvalError>`. Notable behavior:

- `/\` and `\/` short-circuit; quantifiers stop at the first witness or counterexample.
- `\div` and `%` use floored division (the result of `%` has the sign of the divisor).
- `Nat` is `0..100` and `Int` is `-100..100` unless symbolic integers are on (`--symbolic-integers` or cfg `SYMBOLIC_INTEGERS TRUE`), in which case they are `IntSet` values: membership works, enumeration is an error.
- Membership in `SUBSET S`, `[S -> T]`, `Seq(S)`, record sets and set operations over them is decided symbolically without enumerating the set (`helpers::in_set_symbolic`).
- `SUBSET`, `Permutations` and `SubBag` refuse to enumerate past configurable caps (`--max-powerset`, `--max-permutations`, `--max-subbag`).
- Unbounded `CHOOSE x : x \notin S` yields a fresh value, and `CHOOSE x : x = e` yields `e`; other unbounded `CHOOSE` forms are errors.
- Recursive functions (`f[x \in S] == ...`) are evaluated over their whole domain with memoization; the function being defined is found through a thread-local stack of active definitions.
- `eval` grows the stack on demand (`stacker`, 512 KiB red zone, 8 MiB segments) so deeply nested specs do not overflow.

### Successor generation

The default engine (`eval/walk.rs`) walks `Next` over one partial successor, in source order as TLC does: `x' = e` binds `x'` at the conjunct that assigns it, `x' \in S`, `\/`, `\E`, `IF` and `CASE` branch, and a successor is emitted once the relation is discharged with every variable assigned. A variable left unassigned is an error unless `--allow-unassigned-stutter` is given. The same machine with bare (unprimed) variables generates initial states from `Init`. Each `Transition` carries the name of the action (disjunct, operator or label) that produced it.

The legacy engine (`enumerate.rs`, `candidates.rs`) infers candidate values per primed variable and filters the product. It is selected only with `TLA_ENGINE=inference`. In debug builds every successor from either engine is re-checked against `Next`.

### ENABLED

`ENABLED A` is evaluated wherever the state variables are in scope (the checker sets them with `with_state_vars`): in invariants, properties, liveness atoms, and `Next` itself. It reads the current state from the environment and searches for a successor of `A` with the selected successor engine, stopping at the first witness. `ENABLED <<A>>_v` (`is_angle_action_enabled`) also requires `v` to change; `v` is evaluated on the partial successor, so `A` may leave variables outside `v` unassigned.

### Errors

`EvalError` variants: `UndefinedVar`, `TypeMismatch`, `DivisionByZero`, `EmptyChoose`, `DomainError`, `NotEnumerable`, each with an optional span. `checker::eval_error_to_diagnostic` converts them for display, with suggestions for misspelled names.

## Model Checker (`checker.rs`)

### Configuration and results

`CheckerConfig` carries limits (`max_states` default 1,000,000, `max_depth` default 100, optional `max_seconds`), symmetry constants, deadlock and liveness switches, `liveness_engine` (`Tableau` default, `Legacy`), output options (verbosity, JSON, DOT path/mode, trace JSON path), `continue_on_violation`, `count_properties`, cfg `CONSTRAINT`s (`state_constraints`) and `VIEW`, `symbolic_integers`, enumeration caps, `check_refinement`, and the names of cfg `PROPERTY` definitions.

`CheckResult` variants: `Ok`, `InvariantViolation`, `PropertyViolation` (kind `Init` or `Action`), `RefinementViolation`, `LivenessViolation`, `Deadlock`, `InitError`, `NextError`, `InvariantError`, `LivenessError`, `MaxStatesExceeded`, `MaxDepthExceeded`, `MaxTimeExceeded`, `NoInitialStates`, `PrepareError` (`PrepareSpecError`: module load/parse, missing constants, ASSUME failure, non-model-value symmetry set, refinement config, untranslatable liveness property, bad constant substitution).

`CheckStats` records states explored, transitions (also per action), maximum depth, elapsed time, violations per invariant and per property with up to 10 traces each (`--continue`), `--count-satisfying` statistics with per-depth breakdowns, the checked `PROPERTY` names, and the DOT graph when requested as a string.

### BFS

A simplified outline of `check_with_state_vars`:

```
prepare_spec; build SymmetryConfig; resolve refinement alias
build tableau formulas for liveness properties (tableau engine), failing early
for s in init_states(Init):
    check SafetyProperty::Init predicates and refinement Init
    if s violates CONSTRAINT: check invariants on s, do not explore
    insert canonical(s) (keyed by VIEW if any); enqueue
while (idx, depth) = queue.pop_front():
    stop on max_states / max_depth / max_seconds
    check invariants (record or stop) and count properties
    successors = next_states(Next, state)
    no successors and deadlock not allowed -> Deadlock
    for t in successors:
        check [][A]_v action properties on (state, t)
        t outside CONSTRAINT: check invariants on t, remember t for fairness, skip
        check refinement step
        insert canonical(t); record edge (and the renamed target if canonicalization changed it)
        new -> record parent and action, enqueue at depth + 1
run liveness checking if enabled and there is fairness or a liveness property
```

States live in an `IndexSet<State>` (O(1) dedup, stable indices); parents and the action that first reached each state are parallel vectors used to reconstruct the shortest trace. Edges are collected only when liveness checking or DOT export needs them. Progress goes to stderr at 1, 10 and 100 states and then every 1000.

### cfg handling (`config.rs`)

`parse_cfg` reads `INIT`, `NEXT`, `SPECIFICATION`, `CONSTANT(S)` (values or `Name <- Def`), `INVARIANT(S)`, `PROPERTY`/`PROPERTIES`, `SYMMETRY`, `VIEW`, `CONSTRAINT(S)`, `ACTION_CONSTRAINT(S)`, `CHECK_DEADLOCK`, `SYMBOLIC_INTEGERS`, `ALIAS`, `POSTCONDITION`. `apply_config` applies them; `ACTION_CONSTRAINT`, `ALIAS` and `POSTCONDITION` produce "not yet supported" warnings.

- `SPECIFICATION` must have the form `Init /\ [][Next]_v /\ ...` with exactly one `[][Next]_v`. Its `WF`/`SF` conjuncts become fairness; its other temporal conjuncts become `temporal_assumptions`. The tableau engine conjoins the assumptions with each property's negation, so only behaviors satisfying them are searched; the legacy engine ignores them with a warning.
- `PROPERTY` conjuncts are classified by `ast::classify_property`, mirroring TLC's `processConfigProps`: a state predicate is checked on initial states (`SafetyProperty::Init`), `[]P` with `P` at most state level becomes an invariant named after the property, `[][A]_v` is checked on every transition that changes `v` (`SafetyProperty::Action`), and anything else is a liveness property. `\A x \in S` distributes over these. With the tableau engine (`Classification::Syntactic`) the level of `P` in `[]P` comes from `level::LevelAnalysis` (TLC's bound), and `[]A` with `A` an action is an error. A cfg `PROPERTY` turns liveness checking on.
- `CONSTRAINT`: states outside it are checked against invariants but not explored; for liveness they count toward WF/SF enabledness only.
- `VIEW`: states are deduplicated by the view's value (the first state reached is kept). Under symmetry the view is minimized over the symmetry group when the group is small enough.

### Symmetry

`SymmetryConfig::canonicalize` maps each state to a representative: it orders the elements of each symmetric set by first occurrence in the state's values, then renames them to the set's elements in sorted order. Example with model values `p1, p2, p3` symmetric:

```
active = {p1, p3}, queue = <<p2>>  -> order p1, p3, p2 -> active = {p1, p2}, queue = <<p3>>
active = {p2, p3}, queue = <<p1>>  -> order p2, p3, p1 -> active = {p1, p2}, queue = <<p3>>
```

Symmetric sets must consist of model values. `--check-refinement` cannot be combined with symmetry.

### Refinement

`refinement::RefinementSpec` resolves `Alias == INSTANCE M WITH ...` and, during the BFS, requires every initial state to satisfy `Alias!Init` and every transition to satisfy `Alias!Next` or leave the abstract variables unchanged.

## Liveness

Liveness runs after the BFS when `--check-liveness` is given or the cfg has a `PROPERTY`, and the spec has fairness or a liveness property.

### Graph construction

`check_liveness_properties` builds a `StateGraph` from the collected edges and adds a stuttering self-loop to every state that lacks one, since `[][Next]_v` always admits stuttering; fairness then rules out stutter cycles where a fair action stays enabled. An edge whose successor was renamed by symmetry or merged by `VIEW` records the state actually reached (`Edge::renamed`), and actions and step formulas are evaluated on it.

Under `SYMMETRY`, liveness is checked on the graph expanded by the symmetry group (`expand_by_symmetry`): every renaming of every representative, with steps renamed accordingly, built by BFS from the renamed initial states. If the expansion would exceed `--max-states`, or a `VIEW` is also set, it falls back to representative states with a warning. Verdicts are meant to match TLC without `SYMMETRY`, since TLC's symmetry reduction is unsound for liveness.

### Fairness

`liveness::FairnessTable::build` evaluates, once per graph, where each `WF_v(A)`/`SF_v(A)` step `<<A>>_v` is enabled and on which edges it is taken. Enabledness comes from explored edges, then successors outside the `CONSTRAINT`, then, if neither shows it, from `A`'s own successors (`angle_action_enabled_in`); the last check is skipped when `A` is provably a disjunct of `Next` (`is_sub_action`). Quantified fairness (`\A x \in S : WF_v(A(x))`) is expanded per element. `fair_components` performs an Emerson–Lei refinement: components that keep a WF action enabled without taking it are dropped, and for SF the `A`-enabled states are removed and the rest re-decomposed. `witness_cycle` builds a cycle through each fairness obligation, so every reported counterexample is fair.

### Tableau engine (default)

1. `ltl::Builder` translates `¬property ∧ temporal_assumptions` into NNF over atoms (state predicates, which may use `ENABLED`, and `[A]_v` step atoms). `~>`, `=>`, `<<A>>_v`, constant-domain quantifiers, and `WF`/`SF` used as obligations (`[]<>¬ENABLED <<A>>_v ∨ []<><<A>>_v`, `<>[]¬ENABLED <<A>>_v ∨ []<><<A>>_v`) are rewritten during the build. A bare state predicate as a property is read as `[]<>P`.
2. `ltl_check::compile` splits the top-level disjunction (up to 64 disjuncts) and builds a Manna–Pnueli tableau for each with `tableau::build` (at most 4096 nodes).
3. `ltl_check::find_behavior` searches the product of the state graph and the tableau for a reachable fair strongly connected set that fulfills every eventuality, reusing the `FairnessTable` through the product's projection onto states and edges. A hit becomes a lasso (prefix + cycle).

Formulas are built before the BFS, so an untranslatable property is reported as `PrepareSpecError::LivenessProperty` without exploring.

### Legacy engine

`--liveness-engine legacy` (the behavior before 0.16) checks only `[]<>P`, `<>P`, `<>[]P` and `P ~> Q` over state predicates (`liveness::find_violation`), with `[](P => <>Q)` read as `P ~> Q`. It classifies `PROPERTY` by rewriting (`Classification::Rewriting`).

### Verification against TLC

`tests/liveness_corpus/` holds specs, cfgs and a `manifest.json` of verdicts produced by TLC. `tests/liveness_oracle.rs` runs every case under both engines and re-validates each reported lasso with an independent evaluator (`tests/liveness_oracle/lasso.rs`); cases with a known divergence carry an xfail marker that must be removed once they agree. `scripts/liveness-oracle.sh` (needs `TLA2TOOLS` pointing to `tla2tools.jar`) re-derives the verdicts with TLC.

## Scenario Exploration (`scenario.rs`)

A scenario is a list of lines:

```
step: x' > x
step: "s1" \in active'
action: NTPSync
action: Cadence; tampered' = TRUE
```

`step:` picks a transition satisfying the expression (unprimed names refer to the current state, primed to the next). `action:` pins the transition to a named action, optionally with a further condition. `execute_scenario` replays the steps from each initial state in turn until one admits the whole scenario, reporting the available actions where a step finds no match. `execute_scenario_stuttering` additionally allows a bounded number of unobserved transitions between steps.

## Interactive Mode and Presenter

The TUI (`ratatui` + `crossterm`) has three entry points:

- `run_interactive` (`--interactive`): choose among enabled actions from any state, step back, and evaluate expressions in a REPL against the current state.
- `run_interactive_replay` (`--replay FILE`): step through a saved counterexample (`--save-counterexample`) with `n`/`p` or the arrow keys.
- `run_presentation` (`--present FILE`): step through a demo manifest's beats and variants.

## Demo Manifests

A manifest (`demo::Manifest`) names variants (spec, optional cfg, constants) and beats (title, note, a scenario or a replay file, a variant or a `compare` list, and `expect` / `expect_per_variant` assertions of the form `final:`, `all:`, `never:`, `step N:`). `demo::run_beat` loads each variant with `load::prepare_from_path`, replays the beat, and evaluates the assertions on the resulting trace. The same reports drive the CLI (`--present` with `--validate`, `--export-md`, `--export-html`, `--explorable`) and the MCP demo tools. The explorable HTML embeds the wasm engine and drives it through the `explore_*` bindings.

## MCP Server

`tla-mcp` (`src/bin/tla_mcp.rs`) serves the Model Context Protocol over stdio with `rmcp`. Tools:

| Tool | Runner function |
|------|-----------------|
| `validate_spec` | Parse and summarize (variables, constants with resolved values, invariants, warnings) |
| `list_invariants` | Invariants that `check_spec` will check |
| `check_spec` | Model check with required `max_states`, `max_depth`, `max_seconds` |
| `replay_scenario` | Scenario replay |
| `validate_demo`, `append_beat`, `export_demo_doc`, `export_demo_html` | Demo manifest tooling |

Each tool deserializes a `schema.rs` input type and calls the matching `mcp::runner` function; long-running tools run on `tokio::task::spawn_blocking`. `runner::prepare` mirrors the CLI pipeline (parse, `merge_extended_declarations`, auto-discovered or explicit cfg via `apply_config`, constants) with `quiet` output, and `check_spec` then calls `checker::check` and maps the `CheckResult` to a tagged `CheckOutcome` (`ok`, `invariant_violation`, `property_violation`, `deadlock`, `liveness_violation`, `limit_reached`, `error` with a `phase`, …). Outputs carry `schema_version` (`mcp::SCHEMA_VERSION`). The server exits on SIGTERM/SIGINT, and on Linux it requests SIGTERM when its parent process exits.

## WASM

`src/wasm.rs` (feature `wasm`) exposes:

- Checking: `check_spec`, `check_spec_with_config`, `check_spec_with_cfg`, `check_spec_with_options`, each returning a JSON `WasmCheckResult` (`success`, `error_type`, `error_message`, `states_explored`, `trace`, `dot`, `warnings`).
- Exploration: `explore_init` (initial states), `explore_next` (transitions from a state), `explore_eval` (an expression in a state) and `explore_invariants` (invariant results in a state). Each takes the spec source, cfg source and constants (and, except `explore_init`, a JSON state) and returns JSON. These back the explorable HTML export.

The WASM build has no filesystem: module loading from disk, DOT/trace file output and the modules listed under Crate Structure are excluded. See [WASM.md](WASM.md).

## Module System

- `INSTANCE M` / `I == INSTANCE M WITH p <- e`: `ModuleRegistry` loads `M.tla` from the spec's directory; `resolve_instances` applies the substitutions to `M`'s definitions (`substitution::apply_substitutions`) and stores them in a thread-local map consulted by `QualifiedCall`.
- Parameterized `I(x) == INSTANCE M WITH ...`: stored as a template (`ParameterizedInstance`); parameters and substitutions are applied at each `I(v)!Op` call.
- `EXTENDS` of user modules: merged into the spec after parsing (`merge_extended_declarations`) and loaded again by `prepare_spec` for evaluation. Redefining an extended operator is accepted (the extending module wins).
- Standard modules named in `EXTENDS` or `INSTANCE` are handled by `stdlib.rs` and the evaluator rather than loaded from files.

## Output and Export

- Human output: `format_trace_with_actions` prints each state with the action that produced it; `--verbose` adds detail.
- JSON: `check_result_to_json` (`--json`).
- `--trace-json` writes the counterexample trace; `--save-counterexample` writes it with spec path, invariant and actions for `--replay`; `trace_io` converts values for both.
- `--export-dot` writes the state graph through `export::export_dot` in the selected `--dot-mode`.

## Testing

```
tests/
├── oracle.rs                       # specs under test_cases/ (pass, violate, error, walker probes, official examples)
├── liveness_oracle.rs              # TLC-confirmed liveness corpus, both engines
├── liveness_oracle/lasso.rs        # independent lasso validator used by liveness_oracle.rs
├── liveness_corpus/                # specs/, cfgs/, manifest.json
├── liveness_regressions.rs         # liveness regression cases
├── cfg_temporal_property_dispatch.rs  # PROPERTY classification under both engines
├── mcp_integration.rs              # MCP runner functions called in-process
├── cli_version.rs                  # --version/--help of the built tla and tla-mcp binaries
├── action_labels.rs, enabled_in_next.rs, primed_calls.rs, primed_operators.rs,
│   scenario_initial_states.rs, scenario_stuttering.rs
└── explorer/                       # Playwright test of the exported explorable HTML (see its README)

test_cases/
├── should_pass/  should_violate/  should_error/  official/
├── walker/  primed_calls/  demo/
└── benchmark/                      # specs used by benches/model_checking.rs
```

```bash
cargo test                          # unit and integration tests
cargo test --test oracle            # spec oracle
TLA_ENGINE=inference cargo test --test oracle   # the oracle under the legacy successor engine
cargo bench                         # Criterion benchmarks (benches/model_checking.rs)
```

`scripts/regression-sweep.sh [BASELINE_REF] [SAMPLES_DIR] [MAX_STATES]` builds a baseline ref and the working tree and compares their normalized output over a directory of sample specs; any difference in a result line is a behavior change to explain. `scripts/liveness-oracle.sh` is described under Liveness.

## Performance Notes

- `IndexSet<State>` gives O(1) deduplication with stable indices for parent pointers and edges.
- `State` is a `Vec<Value>` indexed by variable position, and `Value` collections are `Arc`-shared, so cloning a state copies pointers rather than collections.
- `Env` is a linear association list with an `Arc` pointer-equality fast path; interned names make that path the common one.
- Edges are collected only when liveness checking or DOT export needs them.
- Symmetry reduction and `VIEW` reduce the explored state space; the liveness check under symmetry works on the expanded graph and is bounded by `--max-states`.
- Successor generation, deduplication and parent bookkeeping are sequential; the checker is single-threaded.
- `--features profiling` reports time spent in `init_states` and `next_states`; `--features dhat` profiles heap allocation.
