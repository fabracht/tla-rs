# Biochemical Pathway Modeling with TLA+

## Thesis

Biochemical pathways are distributed systems. Metabolite pools are shared resources. Enzyme-catalyzed reactions are concurrent processes competing for those resources. Conservation laws (mass, charge, cofactor pools) are invariants that must hold across all reachable states. TLA+ model checking can verify these properties exhaustively and catch bugs that correspond to biochemically impossible events.

## Analogy Table

| Biochemistry | Distributed Systems (TLA+) |
|---|---|
| Metabolite pool (ATP, NAD+, glucose) | Shared variable (integer counter) |
| Enzyme-catalyzed reaction | Action (state transition) |
| Substrate availability | Guard condition (precondition) |
| Conservation of mass | Global invariant |
| Cofactor recycling (NAD+/NADH) | Resource pool with bounded capacity |
| Pathway deadlock (no substrate for any enzyme) | Deadlock state (no enabled actions) |
| Metabolic steady state | Terminal state / fixed point |
| Reaction stoichiometry | Variable update magnitudes |
| Enzyme specificity | Action guards selecting specific substrates |
| Metabolic flux | Transition frequency across state space |

## Abstraction Decisions

Glycolysis has 10 enzymatic steps. We consolidate into 5 actions:

| Action | Steps | What Happens | Why Merge |
|---|---|---|---|
| Phosphorylation | 1-3 (hexokinase, PGI, PFK-1) | glucose → F1,6BP, consuming 2 ATP | Steps 2 is an isomerization (G6P→F6P) with no resource effect. The two ATP-consuming steps (1, 3) are the interesting ones. |
| Split | 4 (aldolase) | F1,6BP → 2 G3P | Step 5 (TPI) just equilibrates the two triose phosphates — we model both as G3P directly. |
| Oxidation | 6 (G3PDH) | G3P → BPG, consuming NAD+ | This is the only step that touches the NAD+/NADH pool. |
| FirstSubstrateLevelP | 7 (PGK) | BPG → PEP, producing ATP | Steps 8-9 are isomerizations (3PG→2PG→PEP). The ATP production in step 7 is what matters. |
| SecondSubstrateLevelP | 10 (pyruvate kinase) | PEP → pyruvate, producing ATP | Final ATP-producing step. |

Key principle: we merge steps that are simple isomerizations (no resource consumption/production) with their adjacent resource-affecting step. This preserves all resource contention behavior while cutting the variable count roughly in half.

## Variables (10)

Metabolite intermediates: `glucose`, `f16bp`, `g3p`, `bpg`, `pep`, `pyruvate`
Cofactor pools: `atp`, `adp`, `nad`, `nadh`

All non-negative integers bounded by `MaxPool`.

## Invariants (6)

- **TypeOK**: all variables in `0..MaxPool`
- **InvATPNonNegative**: `atp >= 0` (trivially true if TypeOK holds, but useful as a standalone check)
- **InvNADNonNegative**: `nad >= 0`
- **InvATPConservation**: `atp + adp = InitATP` (adenine nucleotide conservation — ATP and ADP are never created or destroyed, just interconverted)
- **InvNADConservation**: `nad + nadh = InitNAD` (same for nicotinamide nucleotides)
- **InvCarbonConservation**: total carbon atoms constant (6 per glucose/F1,6BP, 3 per triose)

## Bug Variant: GlycolysisBug_NoATPCheck

Removes the `atp >= 2` guard from Phosphorylation. This models an enzyme that doesn't check whether ATP is available before consuming it — biochemically impossible but a common software bug (consuming a resource without checking availability). With `InitATP=0`, phosphorylation fires anyway, driving ATP negative and violating `InvATPNonNegative`.

## Run Results

### Basic Check (InitGlucose=1, InitATP=2, InitNAD=2, MaxPool=10)

```
Reachable states: 10
Transitions: 11
Max depth: 7
Time: 0.003s
All 6 invariants pass.
```

The state space is tiny — 1 glucose molecule through 5 sequential reactions with constrained cofactor pools produces only 10 reachable states.

### Property Counting (Small Model)

```
ATPPositive:      6/10  (60.0%)   — ATP available in most early states, depleted after phosphorylation
NADAvailable:     6/10  (60.0%)   — NAD+ available early, depleted as oxidation consumes it
PathwayComplete:  0/10  (0.0%)    — pathway NEVER completes (see Observations)
EnergyPayoff:     0/10  (0.0%)    — ATP never exceeds InitATP
Deadlocked:       2/10  (20.0%)   — 2 terminal states at depth 7 (100% of depth-7 states)
```

Depth-stratified highlights:
- ATPPositive drops to 0% at depths 2-4 (right after phosphorylation burns 2 ATP), recovers to 100% at depths 6-7 as substrate-level phosphorylation regenerates ATP
- NADAvailable shows the opposite trajectory: 100% through depth 4, declining to 0% at depth 7 as oxidation consumes all NAD+

### Bug Variant (InitGlucose=1, InitATP=0, InitNAD=2, MaxPool=10)

```
12 invariant violations across 10 states:
  TypeOK: 6 violations
  InvATPNonNegative: 6 violations
```

Counterexample trace: Phosphorylation fires with `atp=0`, producing `atp=-2`. The missing `atp >= 2` guard allows the reaction to proceed without sufficient cofactor. ATP conservation (`atp + adp = InitATP`) also breaks because the model allows creating ADP from nothing.

### Larger Model (InitGlucose=2, InitATP=4, InitNAD=4, MaxPool=20)

```
Reachable states: 48
Transitions: 88
Max depth: 13
Time: 0.009s
All 6 invariants pass.
```

Property counting:
```
ATPPositive:      39/48 (81.2%)   — higher than small model due to larger pool
NADAvailable:     39/48 (81.2%)   — symmetric with ATP availability
PathwayComplete:   0/48 (0.0%)    — STILL never completes
EnergyPayoff:      0/48 (0.0%)    — ATP never exceeds InitATP
Deadlocked:        3/48 (6.2%)    — 3 terminal states at depth 13
```

NADAvailable depth profile is the inverse of ATPPositive: starts at 100%, declines to 0% at depth 13. This reflects the sequential nature of the pathway — ATP is consumed early and regenerated late, while NAD+ is consumed in the middle and never recycled (no fermentation or oxidative phosphorylation in this model).

### DOT Export

State graph exported to `glycolysis_small.dot` (10 nodes, 11 edges). The graph is a near-linear chain with one branch point where two G3P molecules can be processed in either order through oxidation.

## Observations

### The ADP Bottleneck

The most striking result: **PathwayComplete is 0% across all model sizes.** The pathway can never fully convert glucose to pyruvate.

Why: Glycolysis consumes 2 ATP in the investment phase (Phosphorylation) and produces 4 ATP in the payoff phase (2× FirstSubstrateLevelP + 2× SecondSubstrateLevelP). Each substrate-level phosphorylation consumes 1 ADP. With `InitATP=2`:

1. Phosphorylation: 2 ATP → 0 ATP + 2 ADP
2. Split: F1,6BP → 2 G3P
3. 2× Oxidation: 2 G3P → 2 BPG (using 2 NAD+)
4. First substrate-level P on BPG₁: 1 ADP → 1 ATP (now: 1 ATP, 1 ADP)
5. Second substrate-level P on PEP₁: 1 ADP → 1 ATP (now: 2 ATP, 0 ADP)
6. **STUCK**: BPG₂ needs ADP for FirstSubstrateLevelP, but ADP = 0

The total ADP available is `InitATP` (when all ATP is consumed). But the payoff phase needs 4 ADP (2 first + 2 second per glucose). With `atp + adp = InitATP`, the maximum ADP at any point is `InitATP`. Since each substrate-level phosphorylation converts ADP→ATP, we can only perform `InitATP` such reactions before exhausting ADP. For 1 glucose we need 4, so we need `InitATP ≥ 4` just to have enough ADP — but even then, the reactions compete for the same pool.

Even with `InitATP=4`: after phosphorylation (2 ATP, 2 ADP), two first substrate-level P's consume both ADPs (4 ATP, 0 ADP), and the two second substrate-level P's can't fire.

This is biochemically accurate for a **closed system**. In real cells, ATP is continuously consumed by other processes (muscle contraction, ion pumps, biosynthesis), regenerating ADP. Our model has no ATP consumers, so the ADP pool is a strict bottleneck. This is exactly the kind of insight exhaustive model checking reveals — a resource recycling dependency that might be missed in simulation.

### NAD+ Follows the Same Pattern

NAD+ is consumed by Oxidation and never regenerated. In real cells, fermentation (anaerobic) or the electron transport chain (aerobic) recycles NADH→NAD+. Without those downstream pathways, NAD+ is a consumable resource, not a recyclable one. The depth-stratified breakdown shows NAD+ declining monotonically as oxidation proceeds.

### Conservation Laws Hold Perfectly

All three conservation invariants (ATP, NAD, carbon) hold across every reachable state in both model sizes. This validates the stoichiometry of the spec — every reaction that consumes a cofactor produces the corresponding counterpart.

### Next Steps

1. **Add fermentation**: A `Fermentation` action converting pyruvate + NADH → lactate + NAD+ would close the NAD+ recycling loop
2. **Add an ATP consumer**: A generic `ATPase` action converting ATP → ADP would model cellular ATP consumption and close the ADP recycling loop
3. **With both additions**: PathwayComplete and EnergyPayoff should become satisfiable, and the model would capture the full metabolic cycle
4. **Krebs cycle**: Model the TCA cycle as a downstream consumer of pyruvate, producing more NADH (and requiring its own recycling via oxidative phosphorylation)
