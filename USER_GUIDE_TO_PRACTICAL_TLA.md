# Practical TLA+ with tla-rs

This guide covers strategies for using TLA+ to find real bugs, validate designs, and understand system behavior. It draws from experience applying tla-rs to distributed protocols, MQTT access control, biochemical pathways, team dynamics, equipment sync protocols, and collaborative editing systems.

## Starting a New Spec

Start minimal. Model one interaction with the smallest constants that expose the behavior you care about. Two users, one resource, two values. If the bug exists, it usually shows up in under 1,000 states.

```tla
---- MODULE MyProtocol ----
EXTENDS Naturals

CONSTANT Users, Resources
VARIABLES state, owner

Init ==
    /\ state = [u \in Users |-> "idle"]
    /\ owner = [r \in Resources |-> "none"]

Next ==
    \/ \E u \in Users, r \in Resources: Claim(u, r)
    \/ \E u \in Users, r \in Resources: Release(u, r)

TypeOK ==
    /\ state \in [Users -> {"idle", "active"}]
    /\ owner \in [Resources -> Users \cup {"none"}]

InvExclusiveOwnership ==
    \A r \in Resources:
        owner[r] /= "none" =>
            Cardinality({u \in Users : state[u] = "active" /\ owner[r] = u}) = 1
====
```

Run it:
```bash
tla spec.tla -c 'Users={"u1","u2"}' -c 'Resources={"r1"}' --allow-deadlock
```

If the invariant holds with 2 users and 1 resource, add a second resource. If it still holds, you probably have the right design. If the state space explodes, that tells you something too — the constraint you removed was load-bearing.

## Naming Invariants

tla-rs auto-detects invariants by name prefix. Definitions starting with `Inv`, `TypeOK`, or `NotSolved` are checked automatically. Everything else is just a definition.

`TypeOK` checks that variables stay in their expected domains. Write it first — it catches modeling errors before you get to the interesting invariants.

`InvSomething` is your safety property. Write it as the thing that must never be false. If you find yourself writing "there should never be two owners," that's `InvExclusiveOwnership`.

`NotSolved` is for reachability puzzles (DieHard, N-Queens). The checker finds the invariant violation, and the counterexample trace is the solution.

## Bug Hunting

The most effective bug-hunting technique is comparative analysis: write the correct spec, then create a variant that removes exactly one guard or precondition. The difference in behavior reveals what that guard was protecting.

For an ownership protocol with compare-and-swap:
```bash
# Correct spec — should pass
tla spec.tla -c 'Users={"u1","u2"}' --allow-deadlock

# Bug variant — remove the CAS check, should violate InvOwnershipSafety
tla bugs/spec_no_cas.tla -c 'Users={"u1","u2"}' --allow-deadlock --continue
```

The `--continue` flag is critical for bug hunting. Without it, the checker stops at the first violation and you see one trace. With it, you see all violations across the full state space. The difference between "1 violation in 239 states" and "640 violations in 1,668 states" tells you whether the bug is a corner case or a fundamental design flaw.

### Quantifying Bug Severity

Use `--count-satisfying` with `--verbose` to measure how a bug degrades safety across the state space:

```bash
tla bugs/spec_no_cas.tla \
  -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' \
  --allow-deadlock --continue \
  --count-satisfying InvOwnershipSafety --verbose
```

The depth breakdown shows when the bug first manifests. A TOCTOU race might show 100% safety at depths 1-5, then 90.9% at depth 6, dropping to 0% by depth 11. This tells you the bug requires specific interleaving depth to trigger — it won't show up in simple unit tests.

### State Space Size as a Signal

When you remove a precondition and the state space grows dramatically, that constraint was doing heavy lifting. In a collaborative editing spec, removing the delete-requires-lock check increased states from 443 to 10,015 (2,162% growth). Removing the edit-requires-lock check grew states to 2,401 (442% growth). The magnitude tells you which guards to prioritize in implementation.

## Designing New Systems

When designing from scratch, the spec is a laboratory for discovering constraints, not a proof tool for verifying a pre-existing design. Expect to iterate.

A typical arc:

1. Write the happy path. Init, Next with the obvious actions, a TypeOK invariant.
2. Run it. Usually passes. This tells you nothing interesting.
3. Add the safety invariant you actually care about. Run again.
4. It probably still passes because your model is too simple.
5. Add the failure mode: network partition, concurrent request, timeout, stale cache.
6. Now it fails. The counterexample shows you exactly which interleaving breaks safety.
7. Add the guard that prevents it. Run again.
8. It passes. But is the guard sufficient? Add another failure mode.
9. Repeat until you've modeled all the failure modes you can think of.

The constraints that emerge from this process are the design. They weren't obvious upfront — they crystallized from watching the model fail and understanding why.

### Modeling Failure Modes

Every interesting system has at least one of these: network partitions (message loss or delay), concurrent access (two users, one resource), timeouts (action enabled by clock, not by state), stale reads (snapshot diverges from current), and partial failure (operation succeeds on one node, fails on another).

Model these as separate actions in your Next relation. A timeout is just an action with a guard on a counter. A stale read is a snapshot variable that doesn't track the current state. The model checker will find every interleaving of these failure modes with your normal operations.

## Redesigning Existing Systems

When you suspect a bug in an existing system but can't reproduce it, model the system as-is — including the suspected flaw. If the model confirms the violation, the counterexample trace shows you the exact interleaving that triggers it. If it doesn't, your model is missing something (which is also useful information).

After finding the bug, write the fix into the spec and verify it passes. Then write the bug variant (the original behavior) and verify it still fails. Now you have a regression test that lives at the design level.

## Parameter Sweeps

`--sweep` runs the full model check across multiple values of a constant and produces a comparison table:

```bash
tla spec.tla \
  --sweep 'N=2;3;4;5' \
  --count-satisfying InvSafety \
  --allow-deadlock
```

This answers questions like "at what team size does QA starvation become structural?" or "how does retry count affect the probability of double delivery?" Look for cliffs — parameter values where behavior changes sharply. If going from N=2 to N=3 drops safety from 100% to 62%, that's the threshold your implementation needs to handle.

Sweep results from a team dynamics model showed that `EscalatedCost` had a binary threshold: the jump from 1 to 2 cost 9.4 percentage points of churn, but 2 to 3 added only 0.1pp. Initial resilience was linear: each point bought roughly 3pp churn reduction. These are the kind of insights that change design decisions.

## Interactive Exploration

Use `-i` for interactive mode when you want to understand a system's behavior rather than just verify it. You can step through transitions manually, evaluate expressions in the current state, test hypotheses about guards, and trace variable changes across history.

```bash
tla spec.tla -c 'Density=3' --allow-deadlock -i
```

Key bindings: arrow keys to select actions, Enter to take an action, `b` to backtrack, `e` for the REPL, `t` for variable trace, `h` for hypothesis testing, `g` to show guard conditions. When an action has many changes, Right arrow or Space expands the details.

Interactive mode is especially useful for understanding counterexample traces. After a model check finds a violation, replay the trace interactively to see exactly what went wrong at each step.

## Scenarios

Drive the checker along a specific execution path using TLA+ predicates:

```bash
tla spec.tla --scenario "step: state'[\"u1\"] = \"active\"
step: owner'[\"r1\"] = \"u1\"
step: state'[\"u2\"] = \"active\""
```

Each `step:` line is a TLA+ expression over current (unprimed) and next-state (primed) variables. The checker finds a transition matching each predicate in sequence. Use this to validate that a specific path exists in your model — "can we actually reach the state we think we can?" — or to set up a specific scenario before switching to free exploration.

## Constant Sizing

State spaces grow combinatorially with constants. Some rules of thumb from real specs:

| Domain | Small (fast) | Medium | Large (slow) |
|--------|-------------|--------|--------------|
| Users/Processes | 2 | 3 | 4+ |
| Resources/Items | 1 | 2 | 3+ |
| Sequence numbers | 2-3 | 4-5 | 6+ |
| Queue depth | 1-2 | 3 | 4+ |

Two users and one resource usually suffice to find concurrency bugs. The model checker explores all interleavings, so even with small constants the state space covers cases that would take millions of random tests to hit.

If your spec takes more than a few seconds, use `--quick` (10,000 state limit) during development and full exploration for final verification. Use `--symmetry` on symmetric constants — if your users are interchangeable, `--symmetry Users` can cut the state space dramatically.

## Practical Patterns

### Pure Functions Don't Need State

If you're verifying a pure function (access control check, validation logic), don't model a test harness that accumulates results. Each invocation is independent. Model it as: Init picks any input, evaluates the function, records the result. The state space is 1 + (number of inputs), not a combinatorial explosion of test sequences. An MQTT ACL verification went from 56,000 states to 22 states this way.

### Sequence Numbers Are Non-Negotiable

In any async system with multiple channels, messages can arrive out of order. Without sequence numbers, old data overwrites new. This showed up in sync routing (buffered mutation with seq=1 arriving after snapshot with seq=5), equipment sync (metadata signaling version 2 while broker holds version 1), and outbox dispatch (re-delivery after progress lost on failure). Every time, the fix was a sequence number guard.

### Phase Ordering Prevents Corruption

Operations that depend on external state (locks held by others, session validity, ownership) must verify-then-act. Skipping verification corrupts shared state. This pattern appeared in offline editing (must reclaim locks before pushing mutations), offline auth (must revalidate session before resuming access), and TOCTOU races (must compare-and-swap, not check-then-write).

### Conservation Laws Catch Missing Mechanisms

In closed systems, define conservation invariants: ATP + ADP = constant, total carbon atoms preserved, messages sent = messages received + in-flight. When the model stalls (a resource accumulates without bound or depletes to zero), it means the spec is missing a mechanism. The model doesn't prove the system is broken — it proves the spec is incomplete.

### Acceptable Tradeoffs vs Real Bugs

Not every invariant violation is a bug. An offline auth system might have 25% of states where the client has access but the server session is invalid. If that window closes on the next server interaction and the risk is bounded, it's a tradeoff, not a vulnerability. Document it: what the gap is, why it's acceptable, how it's mitigated, and what the mitigation latency is. This prevents false alarms and keeps the team focused on real issues.

## Flag Reference for Analysis

| Goal | Flags |
|------|-------|
| Find first bug | `tla spec.tla` |
| Find all bugs | `--continue` |
| Measure safety degradation | `--continue --count-satisfying InvName --verbose` |
| Compare correct vs buggy | Run both, compare violation counts and satisfaction % |
| Sensitivity analysis | `--sweep 'Param=V1;V2;V3'` |
| Explore interactively | `-i` |
| Verify specific path exists | `--scenario @path.txt` |
| Quick iteration during development | `--quick` |
| Reduce symmetric state space | `--symmetry ConstName` |
| Machine-readable output | `--json` |
| Visualize state graph | `--export-dot graph.dot` |
| Check liveness/fairness | `--check-liveness` |

## Compositional Specs with INSTANCE

As specs grow, extract reusable components into separate modules. A channel abstraction, a lock protocol, or a queue can live in its own `.tla` file and be instantiated with different parameters.

```tla
---- MODULE MChannel ----
CONSTANT Id, Data
VARIABLE channels

Send(data) ==
   /\ \lnot channels[Id].busy
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val = data, !.busy = TRUE]]

Recv(data) ==
   /\ channels[Id].busy
   /\ data = channels[Id].val
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val = <<>>, !.busy = FALSE]]

InitValue == [val |-> <<>>, busy |-> FALSE]
====
```

The main spec instantiates it with concrete parameters:

```tla
ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

ServerSendPing ==
   /\ \E client_id \in ClientIds:
      ServerToClientChannel(client_id)!Send([message |-> "ping"])
   /\ UNCHANGED<<client_to_server>>
```

Each qualified call like `ServerToClientChannel(1)!Send(msg)` substitutes `Id=1` and `channels=server_to_client` into the module body, then evaluates `Send(msg)` in that context.

The module file must be in the same directory as the main spec. Library modules (no Init/Next) work as INSTANCE targets. Stdlib modules (Naturals, Sequences, TLC) can be used with `LOCAL INSTANCE` inside any module.

```bash
tla pingpong.tla -c NumberOfClients=2 -c NumberOfPings=2 --allow-deadlock
```

## Stack Size

Complex specs with deeply nested function access patterns (like `store[id][field][subfield]`) may need a larger stack. If you get a stack overflow, set:

```bash
RUST_MIN_STACK=33554432 tla spec.tla ...
```

This gives 32MB of stack, which handles most real-world specs.
