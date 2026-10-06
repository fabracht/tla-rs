# TLA+ Syntax Coverage Status

Cross-checked against:
- [tree-sitter-tlaplus grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus)
- [vscode-tlaplus TextMate grammar](https://github.com/tlaplus/vscode-tlaplus)
- [Specifying Systems by Leslie Lamport](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)

---

## Fully Implemented ✓

### Logical Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `/\` | ∧ | Conjunction (AND) |
| `\/` | ∨ | Disjunction (OR) |
| `~` | ¬ | Negation (NOT) |
| `=>` | ⇒ | Implication |
| `<=>` | ≡, ⟺ | Equivalence |
| `\land` | | Conjunction (alias) |
| `\lor` | | Disjunction (alias) |
| `\lnot`, `\neg` | | Negation (aliases) |
| `TRUE`, `FALSE` | | Boolean constants |

### Comparison Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `=` | | Equality |
| `/=`, `#` | ≠ | Inequality |
| `<` | | Less than |
| `>` | | Greater than |
| `<=`, `=<`, `\leq` | ≤ | Less than or equal |
| `>=`, `\geq` | ≥ | Greater than or equal |

### Arithmetic Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `+` | | Addition |
| `-` | | Subtraction / Negation |
| `*` | | Multiplication |
| `/` | | Integer division (aliased to `\div`; warns once — in TLA+ `/` is real division from the Reals module, which TLC cannot evaluate and tla-rs does not support; use `\div`) |
| `\div` | | Integer division |
| `%` | | Modulo |
| `^` | | Exponentiation |
| `..` | | Integer range |
| `\b` | | Binary literals (`\b1010` = 10) |
| `\o` | | Octal literals (`\o17` = 15) |
| `\h` | | Hexadecimal literals (`\hFF` = 255) |

### Set Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `\in` | ∈ | Membership |
| `\notin` | ∉ | Non-membership |
| `\subseteq` | ⊆ | Subset or equal |
| `\subset` | ⊂ | Proper subset |
| `\supseteq` | ⊇ | Superset or equal |
| `\supset` | ⊃ | Proper superset |
| `\union`, `\cup` | ∪ | Union |
| `\intersect`, `\cap` | ∩ | Intersection |
| `\` | | Set difference |
| `\times`, `\X` | × | Cartesian product |
| `SUBSET` | | Powerset |
| `UNION` | | Distributed union |
| `{x \in S : P}` | | Set filter |
| `{e : x \in S}` | | Set map |
| `{<<x, y>> \in S : P}` | | Set filter with tuple binder |
| `{e : <<x, y>> \in S}` | | Set map with tuple binder |
| `Cardinality(S)` | | Set cardinality (FiniteSets) |
| `IsFiniteSet(S)` | | Finiteness test (FiniteSets) |

### Quantifiers
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `\A x \in S : P` | ∀ | Universal |
| `\E x \in S : P` | ∃ | Existential |
| `\A x, y \in S : P` | | Multiple variables sharing a domain |
| `\E x \in S, y \in T : P` | | Multiple independent bindings |
| `\E <<x, y>> \in S : P` | | Tuple-binding destructuring (also `\A`, set comprehensions, `CHOOSE`, fn def) |
| `CHOOSE x \in S : P` | | Bounded Hilbert choice |
| `CHOOSE x : x \notin S` | | Unbounded — picks a fresh `MODEL_VALUE_i` not in S |
| `CHOOSE x : x = e` | | Unbounded — returns `e` (when `e` is independent of `x`) |

### Function Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `[x \in S \|-> e]` | | Function definition |
| `[<<x, y>> \in S \|-> e]` | | Function definition with tuple binder |
| `f[x]` | | Function application |
| `DOMAIN f` | | Function domain |
| `[f EXCEPT ![a] = b]` | | Function update |
| `@` | | Self-reference in EXCEPT |
| `[S -> T]` | | Function set |
| `@@` | | Function merge |
| `:>` | | Single function constructor |
| `\|->` | ↦ | Maps-to |
| `->` | → | Arrow (in function sets) |
| `LAMBDA x : e` | | Anonymous function |

### Sequence Operators
| ASCII | Description |
|-------|-------------|
| `<<a, b, c>>` | Tuple/sequence literal |
| `s[i]` | Element access |
| `Len(s)` | Length |
| `Head(s)` | First element |
| `Tail(s)` | All but first |
| `Append(s, e)` | Append element |
| `\o` | Concatenation (disambiguated from octal by context) |
| `SubSeq(s, m, n)` | Subsequence |
| `SelectSeq(s, Test)` | Filter sequence by predicate |
| `Seq(S)` | Set of all sequences (membership tests only, not enumerable) |

### Record Operators
| ASCII | Description |
|-------|-------------|
| `[a \|-> 1, b \|-> 2]` | Record literal |
| `r.field` | Field access |
| `[field1: S1, field2: S2]` | Record set |

### Control Flow
| ASCII | Description |
|-------|-------------|
| `IF P THEN e1 ELSE e2` | Conditional |
| `CASE p1 -> e1 [] p2 -> e2` | Case expression |
| `LET x == e IN body` | Local definition |

### State Operators
| ASCII | Description |
|-------|-------------|
| `x'` | Primed variable (next state); prime distributes over expressions and defined operators, so `Op'` and `(f[i])'` prime every state variable within |
| `UNCHANGED <<x, y>>` | Variables unchanged |

### Relation Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `^+` | ⁺ | Transitive closure |
| `^*` | | Reflexive-transitive closure |

### TLC Operators
| ASCII | Description |
|-------|-------------|
| `Print(val, expr)` | Debug print (outputs to stderr) |
| `PrintT(val)` | Shorthand for Print(val, TRUE) |
| `Assert(cond, msg)` | Assertion (fails if cond false) |
| `ToString(v)` | Convert value to string |
| `SystemTime` | Current time in ms since epoch |
| `JavaTime` | Errors (use SystemTime instead) |
| `Permutations(S)` | All permutations of set (max 10 elements by default; `--max-permutations`) |
| `SortSeq(s, cmp)` | Sort sequence with comparator LAMBDA |
| `RandomElement(S)` | Random element from set (deterministic with seed) |
| `TLCGet(i)` | Get TLC state value at index i, or stats with string keys |
| `TLCSet(i, v)` | Set TLC state value at index i |
| `Any` | Special constant where `v \in Any` for all v |
| `TLCEval(v)` | Force eager evaluation (no-op in tla-rs) |

**TLCGet String Keys:** `"distinct"`, `"level"`, `"diameter"`, `"queue"`, `"duration"`, `"generated"`

### Bags Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `IsABag(B)` | | Check if B is a valid bag |
| `BagToSet(B)` | | Domain of bag (elements with count >= 1) |
| `SetToBag(S)` | | Create bag from set (each element count = 1) |
| `BagIn(e, B)` | | Element membership in bag |
| `EmptyBag` | | Empty bag constant |
| `B1 \oplus B2` | ⊕ | Bag addition (add counts) |
| `B1 \ominus B2` | ⊖ | Bag subtraction (subtract counts) |
| `BagUnion(S)` | | Union of all bags in set S |
| `B1 \sqsubseteq B2` | ⊑ | Bag subset (counts in B1 <= counts in B2) |
| `SubBag(B)` | | Set of all sub-bags of B (max 20 total copies by default; `--max-subbag`) |
| `BagOfAll(F, B)` | | Map function over bag |
| `BagCardinality(B)` | | Sum of all counts |
| `CopiesIn(e, B)` | | Number of copies of e in B |

### Bits Module Operators
| ASCII | Description |
|-------|-------------|
| `BitAnd(a, b)` | Bitwise AND |
| `BitOr(a, b)` | Bitwise OR |
| `BitXor(a, b)` | Bitwise XOR |
| `BitNot(a)` | Bitwise NOT (complement) |
| `ShiftLeft(a, n)` | Left shift by n bits (also `LeftShift`, max 63) |
| `ShiftRight(a, n)` | Right shift by n bits (also `RightShift`, max 63) |

### Module Structure
| Keyword | Description |
|---------|-------------|
| `MODULE` | Module declaration |
| `EXTENDS` | Import module |
| `VARIABLE(S)` | State variables |
| `CONSTANT(S)` | Constants |
| `ASSUME` | Evaluated at startup; aborts if any constraint is FALSE |
| `RECURSIVE` | Recursive operator (stack overflow protected via `stacker`) |
| `INSTANCE M WITH p <- e` | Static module instantiation with substitutions |
| `A(x) == INSTANCE M WITH p <- e` | Parameterized module instantiation |
| `A!Op(args)` | Qualified call to instance operator |
| `A(x)!Op(args)` | Qualified call to parameterized instance operator |
| `LOCAL` | Local definitions and instances (not exported) |
| `Label::` | Action labels (consumed by parser, used for action naming) |

Library modules (modules without Init/Next) are supported for use as instance targets.
Stdlib modules (Naturals, Sequences, TLC, etc.) can be used with `LOCAL INSTANCE`.

### Standard Library Modules
| Module | Status |
|--------|--------|
| `Naturals` | ✓ Nat set (bounded 0..100 by default; infinite symbolic set with `--symbolic-integers`), arithmetic operators built-in |
| `Integers` | ✓ Int set (bounded -100..100 by default; infinite symbolic set with `--symbolic-integers`), includes Nat |
| `Sequences` | ✓ All 8 operators: Len, Head, Tail, Append, \o, SubSeq, SelectSeq, Seq(S) |
| `FiniteSets` | ✓ Cardinality, IsFiniteSet |
| `TLC` | ✓ All 13 operators |
| `Bags` | ✓ All 13 operators |
| `Bits` | ✓ All 6 operators: BitAnd, BitOr, BitXor, BitNot, ShiftLeft, ShiftRight (built-ins, not module exports) |

---

## Parsed But Not Evaluated ⚠️

### Temporal Operators
These operators are parsed into the AST but error at evaluation time. They can appear in skipped definitions (like `Spec`) without causing errors. Fairness operators are handled by the liveness checker (`--check-liveness`); see **Liveness Property Forms** below for how `<>`, `[]<>`, `<>[]`, and `~>` are checked as top-level properties.

| ASCII | Unicode | Description | Status |
|-------|---------|-------------|--------|
| `[]P` | □ | Always | Parsed, errors if evaluated directly |
| `<>P` | ◇ | Eventually | Parsed, errors if evaluated directly |
| `~>` | | Leads-to | Parsed, errors if evaluated directly |
| `WF_v(A)` | | Weak fairness | ✓ Used in liveness checking via SCC analysis |
| `SF_v(A)` | | Strong fairness | ✓ Used in liveness checking via SCC analysis |
| `ENABLED A` | | Action enabled | ✓ In invariants, properties and liveness checking; not in an action that generates states |
| `[A]_v` | | Box action | ✓ As an action (`A \/ UNCHANGED v`), e.g. under `ENABLED`; `[][A]_v` is the temporal form |
| `<<A>>_v` | | Diamond action | Parsed, errors if evaluated directly |
| `\cdot` | | Action composition | Parsed, errors if evaluated directly |

The subscript `v` of `WF_v`, `SF_v`, `[A]_v` and `<<A>>_v` may be a variable, a definition, or any parenthesized expression, tuple or record: `WF_<<x, y>>(A)`, `[A]_(x + y)`, `[A]_[a |-> x]`.

### Tableau Liveness Engine

The tableau engine, the default since 0.16.0 (`--liveness-engine tableau`, MCP `liveness_engine: "tableau"`), checks liveness the way TLC does: it builds the tableau of the property's negation, conjoined with the specification's temporal assumptions, and searches the product of the state graph and the tableau for a fair behavior that satisfies it. Any temporal formula over state predicates and `[][A]_v` / `<<A>>_v` steps is checked, including disjunctions, nested temporal operators (`[](P => []Q)`, `<>(P /\ <>Q)`), negations, `IF` and implications over temporal formulas, conditions on the state (`x = 0 => [](x < 2)`), `\A` / `\E` over constant sets, `ENABLED`, and `WF`/`SF` as obligations (`PROPERTY AInit /\ [][ANext]_v /\ WF_v(A)`). The engine before it, selected with `--liveness-engine legacy`, is described in the sections below marked *legacy engine*; the property classification table applies to both.

With the tableau engine:

- `PROPERTY` conjuncts are classified on their syntax, as TLC does: a state predicate, `[]P` and `[][A]_v` are safety checks as in the table below, and every other conjunct is a liveness property checked whole. `~<>P` is therefore a liveness property, not an invariant. Whether `[]P` is an invariant follows TLC's level bound of `P`: a `LET` counts its definitions as well as its body, and an operator application its arguments as well as the operator's body, used or not, so an action there makes `[]P` a temporal property (`[](LET a == Inc IN ENABLED a)`, `[]En(Inc)`), while `ENABLED` makes its whole operand a state formula (`[](ENABLED Inc)` and `[]En(x)` with a state argument are invariants). `[]P` over an action that is not under `ENABLED` (`[](x' >= x)`, `[]Changed(x)` with `Changed(v) == v' # v`, `[](UNCHANGED y)`) is rejected, as SANY rejects it ("[] followed by action not of form [A]_v"). An operator of an `INSTANCE` (`I!Op`) is taken at the level of its arguments, since the instanced module is not consulted when properties are classified, so `[]I!Op` is an invariant where TLC may find it temporal. The legacy engine classifies a `[]P` that TLC finds temporal as an invariant, reporting the same violation as an invariant violation.
- The `SPECIFICATION`'s temporal conjuncts other than `WF`/`SF` are enforced as assumptions: only behaviors that satisfy them are checked.
- The `SPECIFICATION`'s assumptions may have any temporal shape (`\E x \in S : <>[]P`, `P => <>Q`, `~<>[]P`, calls to temporal operators); with either engine they are no longer folded into the initial predicate.
- A property is translated, and its tableau built, before the state search; one it cannot express is reported as `liveness_property_error`: one that uses `TLCGet`, `RandomElement` or the time built-ins (their value depends on the run, not on a state). `ENABLED` may appear in state predicates; `ENABLED A` holds when `A` has a successor from the state, and `ENABLED <<A>>_v` when one of those successors changes `v` (`A` may leave unassigned only variables that `v` does not depend on, as in TLC). An operator passed as an argument to another operator (`Gen(A(_), k) == ENABLED A(k)`) is not supported. `WF_v(A)` inside a property is an obligation, checked as `[]<>~ENABLED <<A>>_v \/ []<><<A>>_v`, and `SF_v(A)` as `<>[]~ENABLED <<A>>_v \/ []<><<A>>_v`. As in TLC, the top of the negation is split into disjuncts searched one at a time, and conjuncts `[]<>p` and `<>[]p` over a state formula `p` are conditions on the accepting cycle rather than tableau formulas, so a conjunction of many of them stays cheap; a disjunct whose remaining tableau needs more than 4096 nodes is rejected as too large.
- Known differences from TLC: when one search level holds both a state violating a `[]P` conjunct and a transition violating a `[][A]_v` conjunct, tla-rs may report the action property where TLC reports the invariant (the verdict is the same); tla-rs accepts action formulas, `WF`/`SF` included, anywhere in a temporal formula, where TLC accepts only `[]<>A` and `<>[]A`; under `SYMMETRY`, liveness is checked on the graph expanded by the symmetry group (every renaming of every reachable representative state), so tla-rs gives the verdict TLC gives without `SYMMETRY`, while TLC with `SYMMETRY` can report violations that do not exist or miss ones that do (it warns that symmetry is unsound for liveness); when the expanded graph would exceed `--max-states`, liveness falls back to the representative states with a warning, where a property stated per element of a symmetric set can be reported violated when it is not. Classification of `\A x \in S : []P(x)` and of operator calls follows current TLC (2026), which treats them as invariants when their level bound, arguments included, is that of a state; TLC 2.19 treated them as temporal properties.

### Property Classification

A cfg `PROPERTY` is split into conjuncts, and each conjunct is checked the way TLC checks it (a bounded `\A x \in S` distributes over the conjuncts of its body):

| Conjunct | Checked as | Reported as |
|----------|-----------|-------------|
| `P` (state predicate) | holds on every initial state | `property_violation`, kind `init` ("violated by the initial state") |
| `[]P` (state predicate) | an invariant, during the safety search | `invariant_violation` naming the property |
| `[][A]_v` | every transition is an `A` step or leaves `v` unchanged | `property_violation`, kind `action` |
| anything else | a liveness property (below), with `--check-liveness`, which a cfg `PROPERTY` turns on | `liveness_violation` naming the property |

With the legacy engine, before classification the property is normalized: operators and `LET` definitions whose bodies are temporal are expanded (parameterized ones included, as are tuple binders `\A <<i, j>> \in S \X S`), `[][]P` and `<><>P` collapse, negation is pushed through `[]`, `<>`, `/\`, `\/`, `=>` and quantifiers (`~<>P` becomes `[]~P`, and is then reported as an invariant violation where TLC reports a temporal property violation), and an antecedent or `IF` condition that does not depend on the state is moved inside the temporal operators (`g => <>P` becomes `<>(g => P)`). A condition depends on the state when it refers to a variable, `ENABLED`, `TLCGet`, `RandomElement` or the time, directly or through definitions. A quantifier around a temporal formula must range over a set that does not depend on the state (TLC rejects it too).

With the legacy engine, any conjunct the checker cannot represent — a `WF`/`SF` formula, an action-level formula other than `[][A]_v`, a temporal formula guarded by a condition on the state (`P => []Q`), or a temporal shape outside the liveness table — is a config-time error rather than being skipped. A disjunction of liveness properties is checked as the conjunction of its disjuncts, which can report a violation that does not exist but never misses one; a disjunction of state predicates is one state predicate; any other disjunction with a temporal disjunct (`x = 1 \/ <>P`, `[]P \/ []Q`) is a config-time error. As in TLC, these checks also cover states and transitions outside a cfg `CONSTRAINT`: such a state is checked against the invariants and initial-state predicates, and the transition into it against the action properties, but it is not explored. A step into such a state also counts toward whether a `WF`/`SF` action is enabled. Under `--continue`, every invariant and action property violation is recorded; an initial-state property violation stops the check, as in TLC. When one state or transition violates several invariants or properties, tla-rs counts each of them, while TLC's `-continue` reports only the first. A successful run lists the properties it checked (`properties_checked` in `--json` and MCP output).

With a cfg `SPECIFICATION`, the specification's temporal conjuncts are assumptions, as in TLC: `WF`/`SF` restrict the checked behaviors to fair ones, and other temporal conjuncts (such as `<>P`) are never checked as properties. The tableau engine enforces those other conjuncts as assumptions; the legacy engine does not restrict the checked behaviors with them, so a liveness violation it reports under such a specification may be one the assumption excludes, which it warns about at load time. Without a cfg that defines the behavior (`SPECIFICATION` or `INIT`/`NEXT`), the temporal conjuncts of `*Spec` definitions are still checked as properties under `--check-liveness`, with a deprecation warning.

### Liveness Property Forms (legacy engine)

With `--check-liveness`, a liveness property is checked against fair behaviors via SCC analysis. Supported forms and the cycle that witnesses a violation:

| Form | Checked as | Violated by |
|------|-----------|-------------|
| `<>P` | Eventually | a fair behavior that never reaches `P`: a path of `¬P` states from an initial state into a fair `¬P` cycle |
| `[]<>P` | Infinitely often | a reachable fair cycle whose states are all `¬P` |
| `<>[]P` | Stable-eventually | a reachable fair cycle containing any `¬P` state |
| `P ~> Q` | Leads-to | a reachable `P ∧ ¬Q` state followed by a path of `¬Q` states into a fair `¬Q` cycle; the `P` state may come before the cycle |
| `[](P => <>Q)` | Leads-to | checked as `P ~> Q` when `P` and `Q` are state predicates |

The liveness graph models the implicit stuttering that `[][Next]_vars` always permits — every state gets a stutter self-loop, and weak/strong fairness rules out the cycles it would otherwise create. An agent that may stall forever therefore needs no explicit `\/ UNCHANGED vars` disjunct to be considered.

Fairness follows TLC. `WF_v(A)` and `SF_v(A)` count only `A` steps that change the subscript `v`, so `WF_x(A)` is vacuous for an `A` that never changes `x`. Whether `A` is enabled in a state is decided from the action itself, as in TLC, so `A` can be enabled where the specification's next-state relation never takes it. A strongly connected set of states that enables `A` but never takes it can still contain a cycle that is fair to `SF_v(A)` by avoiding every `A`-enabled state; such cycles are found and checked. When a cfg defines the behavior with `SPECIFICATION` or `INIT`/`NEXT`, fairness comes only from the named `SPECIFICATION` (none with `INIT`/`NEXT`), never from other `*Spec` definitions in the module.

### Quantified Temporal Properties (legacy engine)

Temporal properties may be quantified over a constant set (requires `--check-liveness`; declared via a cfg `PROPERTY`, or legacy `*Spec` extraction without a cfg).

| Form | Handling |
|------|----------|
| `\A x \in S : <>P(x)` / `\A x \in S : P(x) ~> Q(x)` | Expanded to one liveness property per element of `S`; all must hold. |
| `\A x \in S : []P(x)` / `\A x \in S : [][A(x)]_v(x)` | Checked as the invariant `\A x \in S : P(x)` / one action property per element of `S` (the subscript may depend on `x`). |
| `\E x \in S : <>Q(x)` | Normalized to `<>(\E x \in S : Q(x))` and checked as a single liveness property. |
| `\E x \in S : []<>Q(x)` | Normalized to `[]<>(\E x \in S : Q(x))` and checked as a single liveness property. |
| `\E x \in S : P(x) ~> Q(x)` (other existential bodies) | Not supported. In a cfg `PROPERTY` it is a config error; inside a `SPECIFICATION` it is an assumption that is not enforced. |

`S` must evaluate to a constant set. Without a cfg that defines the behavior, a property whose definition name ends in `Spec` is extracted by the parser, so it is not re-extracted when also named in a cfg `PROPERTY`.

---

## Not Implemented ✗

### Proof Constructs
- `THEOREM`, `LEMMA`, `COROLLARY` - Parsed and skipped
- `PROOF`, `BY`, `QED` - Parsed and skipped
- Proof steps (`<1>1.`, etc.) - Parsed and skipped

### Other Missing
| Feature | Description |
|---------|-------------|
| Unbounded `\E` / `\A` | `\E x : P` / `\A x : P` without domain (the universe cannot be enumerated). Unbounded `CHOOSE` is supported for the `x \notin S` and `x = e` patterns. |

---

## Unicode Support

### Fully Supported
| Unicode | ASCII Equivalent |
|---------|------------------|
| ∧ | `/\` |
| ∨ | `\/` |
| ¬ | `~` |
| ⇒, ⟹ | `=>` |
| ⟺ | `<=>` |
| ∈ | `\in` |
| ∉ | `\notin` |
| ⊆ | `\subseteq` |
| ⊂ | `\subset` |
| ⊇ | `\supseteq` |
| ⊃ | `\supset` |
| ∪ | `\cup` |
| ∩ | `\cap` |
| × | `\times` |
| ≤ | `<=` |
| ≥ | `>=` |
| ≠ | `/=` |
| ∃ | `\E` |
| ∀ | `\A` |
| ⊕ | `\oplus` |
| ⊖ | `\ominus` |
| ⊑ | `\sqsubseteq` |
| ≡ | `<=>` |
| ↦ | `\|->` |
| → | `->` |
| ⁺ | `^+` |
| □ | `[]` |
| ◇ | `<>` |

---

## Coverage Summary

| Category | Coverage |
|----------|----------|
| Logical Operators | 100% ✓ |
| Comparison | 100% ✓ |
| Arithmetic | 100% ✓ |
| Set Operators | 100% ✓ |
| Quantifiers | 100% ✓ |
| Functions | 100% ✓ |
| Sequences | 100% ✓ |
| Records | 100% ✓ |
| Control Flow | 100% ✓ |
| State Operators | 100% ✓ |
| Relation Operators | 100% ✓ |
| TLC Module | 100% ✓ |
| Bags Module | 100% ✓ |
| Bits Module | 100% ✓ |
| Standard Library | 100% ✓ |
| Module System | 100% ✓ |
| Temporal/Liveness | 60% ⚠ |
| Proofs | 0% ✗ |
| Number Formats | 100% ✓ |

---

## Implementation Priority

### Low Priority (Remaining)
1. **Proof constructs** (currently safely skipped)
2. **Unbounded `\E` / `\A`** (`\E x : P` without domain — fundamentally unsupportable for explicit-state checking)

---

## Test Results (Official Examples)

| Spec | Status | Notes |
|------|--------|-------|
| CarTalkPuzzle | ✓ | Logic puzzle |
| DieHard | ✓ | Finds solution (11 states) |
| EWD840 | ✓ | Termination detection (64 states, N=2) |
| Hanoi | ✓ | Tower of Hanoi puzzle |
| HourClock | ✓ | 12 states |
| MissionariesAndCannibals | ✓ | Classic puzzle (64 states) |
| Paxos | ✓ | Large state space |
| Prisoners | ✓ | 74 states |
| Queens | ✓ | N-Queens constraint satisfaction |
| Reachability | ✓ | Graph reachability |
| SimpleAllocator | ✓ | 64 states |
| TCommit | ✓ | Transaction commit (12 states) |
| TwoPhase | ✓ | Two-phase commit (56 states, RM=2) |
| Voting | ✓ | Bounded via `MaxBallot` constant (599 states) |
| Paxos | ✓ | Bounded via `MaxBallot` constant (3921 states) |

---

## References

- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus)
- [vscode-tlaplus](https://github.com/tlaplus/vscode-tlaplus)
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)
- [Learn TLA+](https://learntla.com)
- [TLA+ Summary](https://lamport.azurewebsites.net/tla/summary-standalone.pdf)
- [TLC.tla source](https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLC.tla)
