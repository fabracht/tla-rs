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
tlc-executor spec.tla -c 'Procs={"p1","p2"}' --allow-deadlock --continue
```
Without `--continue`, the checker stops at the first violation. With it, all violations are collected and counted per-invariant across the full state space.

**Count property satisfaction** to measure what fraction of reachable states satisfy a predicate:
```bash
tlc-executor spec.tla -c 'Procs={"p1","p2"}' --allow-deadlock \
  --count-satisfying InvSafety --count-satisfying InvLiveness
```
Reports how many reachable states satisfy each named boolean definition.

**Combine `--continue` with `--count-satisfying` and `--verbose`** to see how a bug degrades safety by depth:
```bash
tlc-executor spec.tla --allow-deadlock --continue \
  --count-satisfying InvSafety --verbose
```
The `--verbose` flag enables per-depth breakdowns showing at which exploration depth violations start appearing.

**A fun example** — C-3PO famously calculates "the possibility of successfully navigating an asteroid field is approximately 3,720 to 1." The spec `examples/c3po_asteroid_field.tla` models the Empire Strikes Back asteroid chase scene with lore-accurate events: variable-damage asteroid impacts, TIE fighter attacks, TIEs getting destroyed by asteroids, hiding in the space slug's cave, mynock damage, escaping the exogorth's mouth, and the only real escape — attaching to a Star Destroyer's hull and floating away with the garbage. No hyperspace: the hyperdrive is dead.

The `Asteroids` constant controls asteroid damage values. Each value becomes an independent action, so `{1,2,3,4,5}` creates 5 strike actions and 5 kill actions competing with ~7 non-asteroid actions — biasing the state space toward destruction.

```bash
tlc-executor examples/c3po_asteroid_field.tla -c 'Asteroids={1,2,3,4,5}' \
  --allow-deadlock --continue \
  --count-satisfying InvNeverTellMeTheOdds \
  --count-satisfying Escaped --verbose
```
```
Model checking complete. 65 invariant violation(s) found across 353 states.

Property statistics:
  InvNeverTellMeTheOdds: 288/353 satisfied (81.6%)
  InvNeverTellMeTheOdds by depth:
    depth   1:      1/1      (100.0%)
    depth   2:      7/7      (100.0%)
    depth   3:     18/18     (100.0%)
    depth   4:     29/34     (85.3%)
    ...
    depth  10:     12/20     (60.0%)
    depth  11:      8/16     (50.0%)
  Escaped: 19/353 satisfied (5.4%)
  Escaped by depth:
    depth   7:      1/60     (1.7%)
    depth   8:      5/55     (9.1%)
    depth  12:      5/9      (55.6%)
    depth  13:      2/2      (100.0%)
```
Only 5.4% of reachable states have the Falcon escaped. Escape requires surviving the asteroid barrage, hiding in the cave, taking mynock damage, escaping the slug's closing mouth (2 shield damage), then waiting for asteroids to destroy all 4 TIE fighters before drifting onto a Star Destroyer's hull. C-3PO's 3,720:1 odds assume probability-weighted paths rather than state counting, but the depth breakdown tells the story: destruction starts at depth 4, escape is impossible before depth 7, and by depth 11 half the remaining states are destroyed.

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

## License

MIT
