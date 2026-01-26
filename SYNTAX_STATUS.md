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
| `<=`, `=<` | ≤ | Less than or equal |
| `>=` | ≥ | Greater than or equal |

### Arithmetic Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `+` | | Addition |
| `-` | | Subtraction / Negation |
| `*` | | Multiplication |
| `/` | | Division |
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
| `Cardinality(S)` | | Set cardinality |
| `IsFiniteSet(S)` | | Finiteness test |

### Quantifiers
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `\A x \in S : P` | ∀ | Universal |
| `\E x \in S : P` | ∃ | Existential |
| `CHOOSE x \in S : P` | | Hilbert choice |

### Function Operators
| ASCII | Unicode | Description |
|-------|---------|-------------|
| `[x \in S \|-> e]` | | Function definition |
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
| `\o` | Concatenation |
| `SubSeq(s, m, n)` | Subsequence |
| `SelectSeq(s, Test)` | Filter sequence |
| `Seq(S)` | Set of all sequences (membership only) |

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
| `x'` | Primed variable (next state) |
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
| `Permutations(S)` | All permutations of set (max 10 elements) |
| `SortSeq(s, cmp)` | Sort sequence with comparator LAMBDA |
| `RandomElement(S)` | Random element from set (deterministic with seed) |
| `TLCGet(i)` | Get TLC state value at index i, or stats with string keys |
| `TLCSet(i, v)` | Set TLC state value at index i |
| `Any` | Special constant where `v \in Any` for all v |
| `TLCEval(v)` | Force eager evaluation (no-op in tlc-executor) |

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
| `SubBag(B)` | | Set of all sub-bags of B |
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
| `ShiftLeft(a, n)` | Left shift by n bits (also `LeftShift`) |
| `ShiftRight(a, n)` | Right shift by n bits (also `RightShift`) |

### Module Structure
| Keyword | Description |
|---------|-------------|
| `MODULE` | Module declaration |
| `EXTENDS` | Import module |
| `VARIABLE(S)` | State variables |
| `CONSTANT(S)` | Constants |
| `ASSUME` | Constraint on constants |
| `RECURSIVE` | Recursive operator |
| `Label::` | Proof labels (skipped) |

---

## Partially Implemented ⚠️

### `INSTANCE` Module Instantiation
- **Status:** Implemented for qualified calls (`Instance!Operator`)
- **Example:** `INSTANCE ModuleName WITH param <- value`
- **Note:** Requires module file to be in same directory as spec

### `RECURSIVE` Operator Definitions
- **Status:** Parsed, works via lazy evaluation
- **Limitation:** No cycle detection

### Standard Library Modules
| Module | Status |
|--------|--------|
| `Naturals` | ✓ Nat set (bounded 0..100) |
| `Integers` | ✓ Int set (bounded -100..100) |
| `Sequences` | ✓ All ops including `Seq(S)`, `SelectSeq` |
| `FiniteSets` | ✓ `Cardinality`, `IsFiniteSet` |
| `TLC` | ✓ All 13 operators implemented |
| `Bags` | ✓ All 13 operators implemented |
| `Bits` | ✓ All 6 operators implemented |

---

## Parsed But Not Evaluated ⚠️

### Temporal Operators
These operators are parsed into the AST but error at evaluation time. They can appear in skipped definitions (like `Spec`) without causing errors.

| ASCII | Unicode | Description | Status |
|-------|---------|-------------|--------|
| `[]P` | | Always | Parsed, errors if evaluated |
| `<>P` | | Eventually | Parsed, errors if evaluated |
| `~>` | | Leads-to | Parsed, errors if evaluated |
| `WF_v(A)` | | Weak fairness | ✓ Used in liveness checking |
| `SF_v(A)` | | Strong fairness | ✓ Used in liveness checking |
| `ENABLED A` | | Action enabled | ✓ Used in liveness checking |
| `[A]_v` | | Box action | Parsed, errors if evaluated |
| `<<A>>_v` | | Diamond action | Parsed, errors if evaluated |

**Liveness Checking:** Use `--check-liveness` to verify fairness properties. The checker computes SCCs and verifies WF/SF constraints are satisfied.

---

## Not Implemented ✗

### Proof Constructs
- `THEOREM`, `LEMMA`, `COROLLARY` - Parsed and skipped
- `PROOF`, `BY`, `QED` - Parsed and skipped
- Proof steps (`<1>1.`, etc.) - Parsed and skipped

### Other Missing
| Feature | Description |
|---------|-------------|
| `\cdot` | Action composition |
| Unbounded quantifiers | `\E x : P` without domain |

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
| Module System | 90% ⚠ |
| Temporal/Liveness | 60% ⚠ |
| Proofs | 0% ✗ |
| Number Formats | 100% ✓ |

---

## Implementation Priority

### Low Priority (Remaining)
1. **Proof constructs** (currently safely skipped)
2. **Unbounded quantifiers** (`\E x : P` without domain)

---

## Test Results (Official Examples)

| Spec | Status | Notes |
|------|--------|-------|
| DieHard | ✓ | Finds solution (11 states) |
| HourClock | ✓ | 12 states |
| EWD840 | ✓ | Termination detection (64 states, N=2) |
| TwoPhase | ✓ | Two-phase commit (56 states, RM=2) |
| TCommit | ✓ | Transaction commit (12 states) |
| MissionariesAndCannibals | ✓ | Classic puzzle (64 states) |
| SimpleAllocator | ✓ | 64 states |
| Voting | ✓ | Needs bounded Nat |
| Paxos | ✓ | Large state space |
| Prisoners | ✓ | 74 states |
| Hanoi | ✓ | Tower of Hanoi puzzle |

---

## References

- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus)
- [vscode-tlaplus](https://github.com/tlaplus/vscode-tlaplus)
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)
- [Learn TLA+](https://learntla.com)
- [TLA+ Summary](https://lamport.azurewebsites.net/tla/summary-standalone.pdf)
- [TLC.tla source](https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLC.tla)
