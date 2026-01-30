# tlc-executor

A fast TLA+ model checker written in Rust.

tlc-executor performs explicit-state model checking of TLA+ specifications, exploring all reachable states to verify that invariants hold. It's designed as a lightweight alternative to the official TLC model checker for specs that fit its supported subset.

## Features

- **Explicit-state model checking** with breadth-first exploration
- **Symmetry reduction** to collapse equivalent states and reduce state space
- **Counterexample traces** with state diffs showing what changed between steps
- **State graph export** to DOT format for visualization
- **Progress reporting** with exploration rate and ETA
- **Helpful error messages** with source locations and suggestions
- **Continue-past-violation mode** to explore the full state space and count all violations
- **Property satisfaction statistics** with depth-stratified breakdowns
- **JSON output** for programmatic consumption of all results

## When to Use

TLA+ model checking is most valuable for:

- **Distributed protocol bugs** where message ordering and interleaving matter
- **Concurrency issues** that are hard to reproduce deterministically
- **Verifying invariants** across many possible execution paths
- **Design validation** before implementing complex state machines
- **Documenting protocols** in a precise, executable format

You probably don't need it for:

- **Straightforward logic errors** (wrong data structure operation, off-by-one)
- **Bugs with obvious root causes** from reading the code or logs
- **Issues confirmable with runtime tests** or instrumentation

If you have metrics showing "processed 139984 of 140000 events" and the fix is changing `map.remove()` to `map.contains()`, just fix it. Save TLA+ for when you're unsure if your fix handles all the edge cases, or when the bug involves subtle timing between concurrent processes.

## Installation

```bash
cargo build --release
```

The binary will be at `target/release/tlc-executor`.

## Usage

```bash
tlc-executor <spec.tla> [options]
```

### Options

| Option | Description |
|--------|-------------|
| `--constant, -c NAME=VALUE` | Set a constant value |
| `--symmetry, -s CONST` | Enable symmetry reduction for a constant |
| `--max-states N` | Maximum states to explore (default: 1000000) |
| `--max-depth N` | Maximum trace depth (default: 100) |
| `--quick, -q` | Quick exploration (limit: 10,000 states) |
| `--export-dot FILE` | Export state graph to DOT format |
| `--allow-deadlock` | Allow states with no successors |
| `--check-liveness` | Check liveness and fairness properties |
| `--continue` | Continue past invariant violations (explore full state space) |
| `--count-satisfying NAME` | Count states satisfying a definition (repeatable) |
| `--scenario TEXT` | Explore a specific scenario (or @file) |
| `--json` | Output results in JSON format |
| `--verbose, -v` | Verbose output (depth breakdowns, etc.) |

### Constant Value Formats

- Integers: `42`, `-7`
- Booleans: `TRUE`, `FALSE`
- Strings: `"hello"`
- Sets: `{1,2,3}`, `{"a","b"}`

### Examples

Check a simple counter spec:
```bash
tlc-executor examples/counter.tla
```

Check with constants:
```bash
tlc-executor spec.tla --constant 'N=5' --constant 'Procs={"p1","p2","p3"}'
```

Enable symmetry reduction for a set of processes:
```bash
tlc-executor spec.tla -c 'Proc={"a","b","c"}' --symmetry Proc
```

Export state graph for visualization:
```bash
tlc-executor spec.tla --export-dot graph.dot
dot -Tpng graph.dot -o graph.png
```

### Scenario Exploration

Explore specific execution paths using TLA+ expressions to match transitions:

```bash
tlc-executor spec.tla --scenario "step: count' = count + 1
step: count' = count + 1
step: count' = count + 1"
```

Or load from a file:
```bash
tlc-executor spec.tla --scenario @scenario.txt
```

Scenario file format:
```
# Comments start with #
step: x' > x                    # x increases
step: "s1" \in active'          # s1 becomes active
step: pc'["p1"] = "critical"    # p1 enters critical section
step: count' = count + 1        # count increments by 1
```

Each `step:` line specifies a TLA+ expression that must be TRUE for the transition. Unprimed variables refer to the current state, primed variables refer to the next state.

### Analytics & Property Statistics

These features are designed for understanding *how* a protocol fails, not just *whether* it fails. They answer questions like "how many states violate safety?" and "at what depth do violations start appearing?"

**Continue past violations** to explore the full state space of a buggy spec:
```bash
tlc-executor test_cases/mqdb/bugs/MQDBOwnershipTOCTOU_BugNoCAS.tla \
  -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' -c 'DataValues={"d1","d2"}' \
  --allow-deadlock --continue
```
```
Model checking complete. 640 invariant violation(s) found across 1668 states.

  Violations by invariant:
    InvOwnershipSafety: 640 violation(s)

  First violation trace (InvOwnershipSafety, 6 states):
    ...

  Reachable states: 1668
  Transitions: 3748
  Max depth: 13
```
Without `--continue`, the checker would stop at the first of those 640 violations after exploring only 239 states.

**Count property satisfaction** to measure what fraction of reachable states satisfy a predicate:
```bash
tlc-executor test_cases/mqdb/MQDBOwnershipTOCTOU.tla \
  -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' -c 'DataValues={"d1","d2"}' \
  --allow-deadlock \
  --count-satisfying InvOwnershipSafety \
  --count-satisfying InvCheckedImpliesOwner
```
```
Property statistics:
  InvOwnershipSafety: 1316/1316 satisfied (100.0%)
  InvCheckedImpliesOwner: 1316/1316 satisfied (100.0%)
```

**Combine `--continue` with `--count-satisfying`** to see how a bug degrades safety across the state space:
```bash
tlc-executor test_cases/mqdb/bugs/MQDBOwnershipTOCTOU_BugNoCAS.tla \
  -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' -c 'DataValues={"d1","d2"}' \
  --allow-deadlock --continue \
  --count-satisfying InvOwnershipSafety --verbose
```
```
Property statistics:
  InvOwnershipSafety: 1028/1668 satisfied (61.6%)
  InvOwnershipSafety by depth:
    depth   1:      4/4      (100.0%)
    depth   2:     16/16     (100.0%)
    ...
    depth   6:    160/176    (90.9%)
    depth   9:    160/336    (47.6%)
    depth  11:      0/104    (0.0%)
```
This shows the TOCTOU bug (missing CAS on commit) starts causing violations at depth 6, and by depth 11 every reachable state is unsafe. The `--verbose` flag enables the per-depth breakdown.

**JSON output** for programmatic use:
```bash
tlc-executor spec.tla --count-satisfying InvSafety --json
```
Returns structured data including `properties` array with `depth_breakdown` per property.

## Supported TLA+ Subset

### Modules

- `Naturals` - Natural numbers (Nat, 0..100)
- `Integers` - Integers (Int, -100..100)
- `Sequences` - Sequence operators
- `FiniteSets` - Finite set operators (Cardinality, IsFiniteSet)
- `TLC` - TLC-specific operators

### Operators

**Logic:** `/\`, `\/`, `~`, `=>`, `<=>`, `TRUE`, `FALSE`

**Comparison:** `=`, `#`, `/=`, `<`, `>`, `<=`, `>=`

**Arithmetic:** `+`, `-`, `*`, `\div`, `%`, `^`

**Sets:** `\in`, `\notin`, `\union`, `\intersect`, `\`, `\subseteq`, `\subset`, `SUBSET`, `UNION`, `Cardinality`, `IsFiniteSet`

**Functions:** `[x \in S |-> expr]`, `f[x]`, `DOMAIN`, `[S -> T]`, `@@`, `EXCEPT`

**Quantifiers:** `\E`, `\A`, `CHOOSE`

**Records:** `[field |-> value]`, `r.field`, `[field: Set]`

**Tuples/Sequences:** `<<a, b, c>>`, `t[i]`, `Len`, `Head`, `Tail`, `Append`, `\o`, `SubSeq`

**Control:** `IF-THEN-ELSE`, `CASE`, `LET-IN`

**State:** `x'` (primed variables), `UNCHANGED`

**Unicode:** `∧`, `∨`, `¬`, `⇒`, `≡`, `∈`, `∉`, `≤`, `≥`, `≠`, `∪`, `∩`, `⊆`, `⊂`, `∃`, `∀`

### Spec Structure

```tla
---- MODULE Example ----
EXTENDS Naturals

CONSTANT N
VARIABLES x, y

Init == x = 0 /\ y = 0

Next ==
    \/ (x < N /\ x' = x + 1 /\ y' = y)
    \/ (y < N /\ x' = x /\ y' = y + 1)

TypeOK == x \in 0..N /\ y \in 0..N
Inv == x + y <= 2 * N
====
```

Invariants are detected by naming convention:
- Names starting with `Inv`
- Names starting with `TypeOK`
- Names starting with `NotSolved`

## Output

### Successful Check
```
Model checking complete. No errors found.

  States explored: 1331
  Transitions: 3630
  Max depth: 31
  Time: 0.019s
```

### Invariant Violation
```
Invariant 0 (Inv) violated!

Counterexample trace (5 states):
  (* marks changed variables)

State 0
  count = 0
State 1
  count = 1 *
State 2
  count = 2 *
...
```

### Deadlock Detection
```
Deadlock detected!

Trace to deadlock state (3 states):
  (* marks changed variables)

State 0
  x = 0
State 1
  x = 1 *
State 2
  x = 2 *

Use --allow-deadlock to suppress this error.
```

### Progress Reporting
Progress is reported early and frequently to provide feedback:
```
  Exploring states...
  Progress: 10 states explored, queue: 23
  Progress: 100 states explored, queue: 156
  Progress: 1000 states (52341/s), queue: 1247, depth: 15, limit ETA: 18.9s
```

For quick exploration without waiting for full verification:
```bash
tlc-executor spec.tla --quick
```
This limits exploration to 10,000 states and exits with success if no violations are found.

### Error Messages
Parse errors show the source location:
```
error: expected identifier, found Eof
  --> spec.tla:5:12
   |
 5 | Next == x' =
   |            ^ expected identifier, found Eof
```

Undefined variables suggest similar names:
```
error: evaluating Next
  undefined variable `coutn`
  help: did you mean `count`?
```

## State Graph Visualization

Export with `--export-dot` and render with Graphviz:

```bash
tlc-executor spec.tla --export-dot graph.dot
dot -Tpng graph.dot -o graph.png
```

Error states are highlighted in red in the generated graph.

## Limitations

- `Nat` and `Int` are bounded (-100 to 100 by default)
- Limited temporal properties (liveness with `--check-liveness`, but not full TLA+ temporal logic)
- Recursive operators must be declared with RECURSIVE

## Design Notes

### Why No Parallel Mode

Parallel state exploration was implemented and removed after benchmarking showed it provided no benefit. The implementation used level-by-level BFS with parallel state evaluation and concurrent deduplication.

**Why it doesn't help:**
- State deduplication and parent pointer maintenance must remain sequential
- Per-state evaluation is fast; most time is spent on state graph management
- Level synchronization overhead exceeds parallelization gains

Benchmarks showed parallel mode was 1.5-2x slower than sequential across all tested specs.

## License

MIT
