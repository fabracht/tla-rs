# tlc-executor

A fast TLA+ model checker written in Rust.

tlc-executor performs explicit-state model checking of TLA+ specifications, exploring all reachable states to verify that invariants hold. It's designed as a lightweight alternative to the official TLC model checker for specs that fit its supported subset.

## Features

- **Explicit-state model checking** with breadth-first exploration
- **Symmetry reduction** to collapse equivalent states and reduce state space
- **Counterexample traces** with state diffs showing what changed between steps
- **State graph export** to DOT format for visualization
- **Progress reporting** with exploration rate and ETA

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
| `--export-dot FILE` | Export state graph to DOT format |

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

### Progress Reporting
For large state spaces, progress is reported every 1000 states:
```
Progress: 10000 states (52341/s), queue: 1247, depth: 15, limit ETA: 18.9s
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
- No temporal properties (only invariants)
- No fairness constraints
- No INSTANCE with parameter substitution
- Recursive operators must be declared with RECURSIVE

## License

MIT
