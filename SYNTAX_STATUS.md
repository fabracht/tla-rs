# TLA+ Syntax Coverage Status

## Implemented ✓

### Values
- [x] Integers: `1`, `42`, `-5`
- [x] Booleans: `TRUE`, `FALSE`
- [x] `BOOLEAN` set: `{TRUE, FALSE}`
- [x] Strings: `"hello"`
- [x] Sets: `{1, 2, 3}`, `{x \in S : P}` (filter), `{e : x \in S}` (map)
- [x] Tuples/Sequences: `<<1, 2, 3>>`
- [x] Records: `[a |-> 1, b |-> 2]`
- [x] Functions: `[x \in S |-> expr]`

### Operators - Logic
- [x] `/\` `\land` - Conjunction
- [x] `\/` `\lor` - Disjunction
- [x] `~` `\lnot` `\neg` - Negation
- [x] `=>` - Implication
- [x] `<=>` - Equivalence

### Operators - Comparison
- [x] `=` - Equality
- [x] `#` `/=` - Inequality
- [x] `<` `>` `<=` `>=` - Comparisons

### Operators - Arithmetic
- [x] `+` `-` `*` `/` `%` - Basic arithmetic
- [x] `\div` - Integer division

### Operators - Sets
- [x] `\in` - Membership
- [x] `\notin` - Non-membership
- [x] `\union` `\cup` - Union
- [x] `\intersect` `\cap` - Intersection
- [x] `\` - Set minus
- [x] `\subseteq` - Subset or equal
- [x] `\subset` - Proper subset
- [x] `\times` `\X` - Cartesian product
- [x] `..` - Integer range
- [x] `SUBSET` - Powerset
- [x] `UNION` - Big union
- [x] `Cardinality` - Set cardinality
- [x] `IsFiniteSet` - Test if set is finite

### Operators - Functions
- [x] `f[x]` - Function application
- [x] `[x \in S |-> e]` - Function definition
- [x] `[S -> T]` - Function set (all functions from S to T)
- [x] `DOMAIN f` - Function domain
- [x] `[f EXCEPT ![a] = b]` - Function update
- [x] `@@` - Function merge
- [x] `:>` - Single-element function

### Operators - Sequences
- [x] `Len(s)` - Length
- [x] `Head(s)` - First element
- [x] `Tail(s)` - All but first
- [x] `Append(s, e)` - Append element
- [x] `\o` - Concatenation
- [x] `SubSeq(s, m, n)` - Subsequence

### Operators - Records
- [x] `r.field` - Field access
- [x] `[field1: S1, field2: S2]` - Record set

### Quantifiers
- [x] `\E x \in S : P` - Existential
- [x] `\A x \in S : P` - Universal
- [x] `\E x \in S, y \in T : P` - Multi-variable quantifiers with different domains
- [x] `\E x, y \in S : P` - Multi-variable quantifiers with same domain
- [x] `CHOOSE x \in S : P` - Choice

### Control Flow
- [x] `IF ... THEN ... ELSE` - Conditional
- [x] `CASE p1 -> e1 [] p2 -> e2` - Case expression
- [x] `LET x == e IN body` - Local definition

### State
- [x] `x'` - Primed variables
- [x] `UNCHANGED <<x, y>>` - Unchanged

### Spec Structure
- [x] `VARIABLES` / `VARIABLE`
- [x] `CONSTANTS` / `CONSTANT`
- [x] `Init == ...`
- [x] `Next == ...`
- [x] `Invariant == ...`
- [x] Operator definitions `Op(x) == ...`

## Partially Implemented ⚠️

### Module System
- [ ] `EXTENDS` - Parsed but modules not loaded
- [ ] `INSTANCE` - Parsed but not substituted
- [ ] `LOCAL` - Parsed but not enforced

### Temporal Operators
- [ ] `[]` (Always) - Lexed as token, not evaluated
- [ ] `<>` (Eventually) - Lexed as token, not evaluated
- [ ] `~>` (Leads-to) - Lexed as token, not evaluated
- [ ] `ENABLED` - Lexed as token, not evaluated

### Proof Constructs (Skipped)
- [ ] `THEOREM`, `LEMMA`, `COROLLARY`
- [ ] `BY`, `DEF`, `QED`
- [ ] `PROVE`, `SUFFICES`, `HAVE`, `TAKE`
- [ ] Proof steps like `<1>1.`

## Not Implemented ✗

### Standard Modules
- [x] `Naturals` - `Nat` set (0..100)
- [x] `Integers` - `Int` set (-100..100)
- [x] `Sequences` - Built-in ops already implemented
- [x] `FiniteSets` - `Cardinality`, `IsFiniteSet` implemented
- [ ] `Reals` - Not applicable for model checking
- [ ] `TLC` - Partial (Print, Assert not implemented)
- [ ] `Bags` - Not implemented

### Advanced Features
- [x] `RECURSIVE` definitions
- [x] `ASSUME` constraints
- [ ] Action composition `A \cdot B`
- [ ] Fairness `WF_vars(A)`, `SF_vars(A)`
- [ ] `SelectSeq` - Sequence filtering

### Operators
- [ ] `\div` vs `/` distinction for integers
- [x] `^` - Exponentiation
- [ ] `$` - Sequences from index
- [ ] `|` - Absolute value / modular

## Gap Analysis (vs tree-sitter-tlaplus grammar)

### Missing Operators - High Priority
| Operator | Symbol(s) | Description | Difficulty |
|----------|-----------|-------------|------------|
| ~~`\subset`~~ | ~~`\subset`, `⊂`~~ | ~~Proper subset (not equal)~~ | ✓ Done |
| ~~`LAMBDA`~~ | ~~`LAMBDA x : e`~~ | ~~Anonymous functions~~ | ✓ Done |
| Unbounded quantifiers | `\E x : P` | Without domain restriction | Medium |
| `^+` | `^+`, `⁺` | Transitive closure | Hard |
| `^*` | `^*` | Reflexive transitive closure | Hard |

### Missing Operators - Low Priority
| Operator | Symbol(s) | Description | Notes |
|----------|-----------|-------------|-------|
| `-+->` | `-+->` | Temporal (stuttering) | Rarely used |
| `<:` | `<:` | Subtype operator | Rarely used |
| `\|\|` | `\|\|` | Parallel composition | Rarely used |
| `-.` | `-.` | Real number negation | Not for model checking |

### Unicode Equivalents (Partially Implemented ✓)
Now supported:
- `∧` for `/\`, `∨` for `\/`, `¬` for `~`
- `⟹`, `⇒` for `=>`
- `∈` for `\in`, `∉` for `\notin`
- `⊂` for `\subset`, `⊆` for `\subseteq`
- `∩` for `\cap`, `∪` for `\cup`, `×` for `\times`
- `≤` for `<=`, `≥` for `>=`, `≠` for `#`
- `∃` for `\E`, `∀` for `\A`

Still missing:
- `⟺`, `⇔` for `<=>`
- `□` for `[]`, `◇` for `<>`
- `⟶`, `→` for `->`, `⟼`, `↦` for `|->`

### Missing Number Formats
- [ ] Binary: `\b1010`
- [ ] Octal: `\o777`
- [ ] Hexadecimal: `\hFF`

### Missing Keywords
- [x] `ASSUMPTION`, `AXIOM` - Aliases for ASSUME ✓
- [x] `LAMBDA` - Anonymous function syntax ✓

### Sequence Operators (from Sequences module)
- [ ] `SelectSeq(s, Test)` - Filter sequence
- [ ] `Seq(S)` - Set of all sequences over S (infinite, needs bound)

### TLC Module
- [ ] `Print(val, expr)` - Debug printing
- [ ] `Assert(cond, msg)` - Assertions
- [ ] `JavaTime` - Current time
- [ ] `ToString(val)` - Value to string
- [ ] `TLCGet/TLCSet` - State variables

### Bags Module
- [ ] `BagIn`, `BagOf`, `BagUnion`, etc.

## Priority Order for Implementation

1. ~~**Standard Modules** (Naturals, Integers, Sequences, FiniteSets)~~ ✓
   - Implemented

2. ~~**RECURSIVE definitions**~~ ✓
   - Implemented

3. ~~**Quick Wins** (Easy additions)~~ ✓ Mostly done
   - ~~`\subset` proper subset~~ ✓
   - `SelectSeq` sequence filtering
   - ~~Unicode operator aliases~~ ✓ (common ones)
   - ~~`ASSUMPTION`/`AXIOM` as ASSUME aliases~~ ✓

4. **Module System** (EXTENDS/INSTANCE)
   - Load and merge module contents
   - Handle substitution for INSTANCE

5. ~~**LAMBDA expressions**~~ ✓
   - ~~Anonymous function syntax~~ ✓

6. **Temporal Logic** (for liveness checking)
   - `[]P` - Always P
   - `<>P` - Eventually P
   - `P ~> Q` - P leads to Q
   - `WF_vars(A)`, `SF_vars(A)` - Fairness

---

## Testing Results (Official TLA+ Examples)

### Specs That Work ✓
| Spec | Status | Notes |
|------|--------|-------|
| DieHard | ✓ Works | Finds solution (violates NotSolved invariant) |
| HourClock | ✓ Works | 12 states explored |

### Specs That Parse But Need Constants
| Spec | Status | Blocker |
|------|--------|---------|
| Voting | ✓ Works | 64 states with bounded Nat={0,1,2} |
| Paxos | ✓ Runs | Large state space, requires bounded Nat |
| SimpleAllocator | ✓ Works | 64 states with 2 clients, 2 resources |
| Prisoners | ✓ Works | 74 states explored (TypeOK invariant checked) |
| Reachability | Parses | Needs function-valued constants |

### Gaps Found from Testing

#### CLI Constant Parsing
- [x] Nested set constants: `{{a,b},{c,d}}` ✓
- [ ] Function-valued constants: `[x |-> y, z |-> w]`
- [ ] Record-valued constants: `[a |-> 1, b |-> 2]`

#### FiniteSets module
- [x] `IsFiniteSet(S)` - Test if set is finite (always true in model checking)

#### Fixed ✓
- [x] `BOOLEAN` set - Now built-in
- [x] `[S -> T]` function sets - Now evaluates correctly
- [x] Non-deterministic Init (`x \in BOOLEAN`) - Works

#### Invariant Detection
- [ ] Only recognizes `Inv`, `Invariant`, or `TypeOK` naming
- [ ] Should detect any definition used as invariant in config
