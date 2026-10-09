# Practical TLA+ with tla-rs

This guide covers strategies for using TLA+ to find real bugs, validate designs, and understand system behavior. It draws from experience applying tla-rs to distributed protocols, MQTT access control, biochemical pathways, team dynamics, equipment sync protocols, and collaborative editing systems.

## Starting a New Spec

Start minimal. Model one interaction with the smallest constants that expose the behavior you care about. Two users, one resource, two values. If the bug exists, it usually shows up in under 1,000 states.

```tla
---- MODULE MyProtocol ----
EXTENDS Naturals, FiniteSets

CONSTANT Users, Resources
VARIABLES state, owner

vars == <<state, owner>>

Init ==
    /\ state = [u \in Users |-> "idle"]
    /\ owner = [r \in Resources |-> "none"]

Start(u) ==
    /\ state[u] = "idle"
    /\ state' = [state EXCEPT ![u] = "active"]
    /\ UNCHANGED owner

Claim(u, r) ==
    /\ state[u] = "active"
    /\ owner[r] = "none"
    /\ \A r2 \in Resources : owner[r2] /= u
    /\ owner' = [owner EXCEPT ![r] = u]
    /\ UNCHANGED state

Release(u, r) ==
    /\ owner[r] = u
    /\ owner' = [owner EXCEPT ![r] = "none"]
    /\ state' = [state EXCEPT ![u] = "idle"]

Next ==
    \/ \E u \in Users: Start(u)
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
tla MyProtocol.tla -c 'Users={"u1","u2"}' -c 'Resources={"r1"}' --allow-deadlock
```

It explores 8 states and both invariants hold. If the invariant holds with 2 users and 1 resource, add a second resource (`-c 'Resources={"r1","r2"}'`: 14 states here, still holding). If it still holds, you probably have the right design. If the state space explodes, that tells you something too — the constraint you removed was load-bearing.

## Naming Invariants

Without a cfg `INVARIANT`, tla-rs auto-detects invariants by name prefix. Definitions starting with `Inv`, `TypeOK`, or `NotSolved` are checked automatically, as are `Inv` and `TypeOK` after a module prefix (`TPTypeOK`, `M_Inv`). Everything else is just a definition. A cfg `INVARIANT` replaces detection: only the definitions it names are checked. `--list-invariants` shows which ones will be checked.

`TypeOK` checks that variables stay in their expected domains. Write it first — it catches modeling errors before you get to the interesting invariants.

`InvSomething` is your safety property. Write it as the thing that must never be false. If you find yourself writing "there should never be two owners," that's `InvExclusiveOwnership`.

`NotSolved` is for reachability puzzles (DieHard, N-Queens). The checker finds the invariant violation, and the counterexample trace is the solution.

## Writing Actions

The shape of your actions determines how readable, scalable, and debuggable your spec is. These patterns come from modeling distributed protocols (TwoPhase, Paxos), team dynamics, equipment sync, and collaborative editing.

### Separate Variables, Not Records

Don't pack all state into one record. The state count is the same either way — a resource allocation spec with the `Advance` action below, an `Assign(u)` action that sets the owner, a `Finish` action that resets phase and owner, 2 users and `count` bounded by 3 produces 13 states and 15 transitions whether you use a single `system` record or three separate variables. But separate variables make each action's footprint obvious: you can see exactly what changes and what doesn't, and UNCHANGED clauses document the scope of every action.

Bad — a single record variable:
```tla
VARIABLE system

Init == system = [phase |-> "idle", count |-> 0, owner |-> "none"]

Advance ==
    /\ system.phase = "idle"
    /\ system' = [system EXCEPT !.phase = "active", !.count = @ + 1]
```

Good — separate variables with explicit UNCHANGED:
```tla
VARIABLES phase, count, owner

Init ==
    /\ phase = "idle"
    /\ count = 0
    /\ owner = "none"

Advance ==
    /\ phase = "idle"
    /\ phase' = "active"
    /\ count' = count + 1
    /\ UNCHANGED <<owner>>
```

The record version hides which fields each action touches. With separate variables, a missing `UNCHANGED` is a checker error ("variable(s) not assigned in action ..."), so you can't accidentally leave a variable unspecified (`--allow-unassigned-stutter` treats an unassigned variable as unchanged instead).

### Managing UNCHANGED

Define a `vars` tuple once at the top of your spec:

```tla
vars == <<phase, count, owner>>
```

Every action must account for every variable — either assign its primed version or list it in UNCHANGED. When you declare a new variable, the checker will flag every action that doesn't mention it, so missing updates surface immediately rather than hiding as silent stuttering.

The TwoPhase spec shows this clearly: `TMCommit` sets `tmState'` and `msgs'`, then explicitly declares `UNCHANGED <<rmState, tmPrepared>>`. Every variable is accounted for in every action.

### Action Decomposition

Break your Next predicate into small, named, parameterized operators. Each action represents one atomic step by one participant.

From TwoPhase:
```tla
RMPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
    /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
    \/ TMCommit \/ TMAbort
    \/ \E rm \in RM :
         TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
           \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
```

Each action has a guard (enabling condition), an effect (primed variable assignments), and an UNCHANGED clause. The `\E rm \in RM` in Next quantifies over participants — one RM takes one step per transition. This pattern scales: adding a new role means adding new actions and one more disjunct in Next.

### LET-IN for Chained Modifications

When one update depends on another in the same step — like completing a task and conditionally resuming the next one — use LET to name the intermediate result:

```tla
FinishTask(t) ==
    /\ taskState[t] = "running"
    /\ LET newState == [taskState EXCEPT ![t] = "done"]
       IN taskState' = IF \E t2 \in Tasks : newState[t2] = "blocked"
                        THEN [newState EXCEPT ![CHOOSE t2 \in Tasks : newState[t2] = "blocked"] = "ready"]
                        ELSE newState
```

The alternative — numbered temporaries like `taskState1`, `taskState2` — clutters the spec and forces you to track which version is "current." LET makes the data flow explicit: compute the intermediate state, then decide what to do next based on it.

### State as Functions

Use `[Key -> Domain]` instead of N separate boolean variables. Functions scale with constants — adding a process doesn't add a variable declaration.

Bad — one variable per process:
```tla
VARIABLES p1_ready, p2_ready, p3_ready

Init ==
    /\ p1_ready = FALSE
    /\ p2_ready = FALSE
    /\ p3_ready = FALSE
```

Good — a function over the process set:
```tla
CONSTANT Proc
VARIABLE ready

Init == ready = [p \in Proc |-> FALSE]

MarkReady(p) ==
    /\ ready[p] = FALSE
    /\ ready' = [ready EXCEPT ![p] = TRUE]
```

EXCEPT works naturally on functions: `[rmState EXCEPT ![rm] = "prepared"]` updates one key and leaves the rest unchanged. The TwoPhase spec models the state of every resource manager this way — `rmState` is a function from `RM` to `{"working", "prepared", "committed", "aborted"}`. Adding a fifth RM means changing the constant, not the spec.

The state space is identical either way — 3 independent booleans and a function `[Proc -> BOOLEAN]` with `|Proc| = 3`, each with the `MarkReady` step above, both produce 8 states and 12 transitions. The advantage is purely structural: the function version doesn't require code changes when you scale up.

### Keep State Flat

Avoid nested records. TLA+ supports `[f EXCEPT ![x][y] = v]` but it's hard to read and error-prone. If you need hierarchy, use composite keys or separate function variables.

Bad — nested records:
```tla
VARIABLE nodes
Init == nodes = [n \in NodeIds |-> [status |-> "up", queue |-> <<>>]]

HandleMsg(n, msg) ==
    /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.queue = Append(@, msg)]]
```

Good — separate function variables:
```tla
VARIABLES nodeStatus, nodeQueue

Init ==
    /\ nodeStatus = [n \in NodeIds |-> "up"]
    /\ nodeQueue = [n \in NodeIds |-> <<>>]

HandleMsg(n, msg) ==
    /\ nodeQueue' = [nodeQueue EXCEPT ![n] = Append(@, msg)]
    /\ UNCHANGED <<nodeStatus>>
```

The flat version is easier to read, each action's scope is obvious from its UNCHANGED clause, and you avoid the `[@ EXCEPT !.field = ...]` nesting that gets unreadable past two levels. Like the record vs. separate variables case, state counts are identical — 2 nodes with `HandleMsg` above, an action that removes the head of a queue, an action that toggles a node's status between up and down, one message value and queues of at most one message produce 16 states and 56 transitions in both the nested and flat versions. The benefit is readability, not performance.

## Bug Hunting

The most effective bug-hunting technique is comparative analysis: write the correct spec, then create a variant that removes exactly one guard or precondition. The difference in behavior reveals what that guard was protecting.

For an ownership protocol with compare-and-swap: each user reads the current `owner` into `seen[u]`, then acquires ownership for one of a set of `Requests`, gives up, or later leaves. The safety property is `InvOwnershipSafety == Cardinality({u \in Users : pc[u] = "owns"}) <= 1`. The correct `Acquire` re-checks the owner at the moment of writing:

```tla
Acquire(u, r) ==
    /\ pc[u] = "read"
    /\ r \notin done
    /\ seen[u] = "none"
    /\ owner = "none"
    /\ owner' = u
    /\ pc' = [pc EXCEPT ![u] = "owns"]
    /\ done' = done \cup {r}
    /\ UNCHANGED seen
```

The bug variant drops the `owner = "none"` conjunct, so a user acts on the value it read earlier (check-then-write):

```bash
# Correct spec — should pass
tla spec.tla -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' --allow-deadlock

# Bug variant — remove the CAS check, should violate InvOwnershipSafety
tla bugs/spec_no_cas.tla -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' --allow-deadlock --continue
```

The correct spec passes in 64 states. The `--continue` flag is critical for bug hunting. Without it, the checker stops at the first violation and you see one trace: here after 20 states. With it, you see all violations across the full state space: 2 violations in 70 states for two users, 36 in 584 states with a third user. How the count grows with the constants tells you whether the bug is a corner case or a fundamental design flaw.

### Quantifying Bug Severity

Use `--count-satisfying` with `--verbose` to measure how a bug degrades safety across the state space:

```bash
tla bugs/spec_no_cas.tla \
  -c 'Users={"u1","u2"}' -c 'Requests={"r1","r2"}' \
  --allow-deadlock --continue \
  --count-satisfying InvOwnershipSafety --verbose
```

The depth breakdown shows when the bug first manifests. For this TOCTOU race, `InvOwnershipSafety` holds in 68 of 70 states (97.1%): in every state at depths 1-4, in 12 of 14 (85.7%) at depth 5, and in every state after. Both users must read the owner before either writes, so the bug needs a specific interleaving four steps deep — it won't show up in simple unit tests.

### State Space Size as a Signal

When you remove a precondition and the state space grows dramatically, that constraint was doing heavy lifting. Compare the reachable state counts of the correct spec and of each single-guard variant: the guard whose removal grows the space the most is the one to prioritize in implementation. Growth is a signal, not a verdict — removing the CAS check above grows the space only from 64 to 70 states, yet it breaks safety.

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
tla bugs/spec_no_cas.tla \
  -c 'Requests={"r1","r2"}' \
  --sweep 'Users={"u1","u2"};{"u1","u2","u3"}' \
  --count-satisfying InvOwnershipSafety \
  --allow-deadlock --continue
```

```
           Users |         states |    transitions |      max_depth |           time | InvOwnershipSafety
-----------------------------------------------------------------------------------------------------
     {"u1","u2"} |             70 |            132 |             10 |         0.002s |  68/70 (97.1%)
{"u1","u2","u3"} |            584 |           1590 |             12 |         0.022s | 548/584 (93.8%)
```

Pass `--continue` when the counted property is also an invariant (an `Inv*` name is detected as one): without it, each run stops at the first violation and the count column reads `n/a`.

This answers questions like "at what team size does QA starvation become structural?" or "how does retry count affect the probability of double delivery?" Look for cliffs — parameter values where behavior changes sharply. If going from N=2 to N=3 drops safety from 100% to 62%, that's the threshold your implementation needs to handle. A threshold can also be a plateau: a cost parameter whose first increment changes the outcome sharply while later increments barely move it is a design decision worth knowing about.

## Interactive Exploration

Use `-i` for interactive mode when you want to understand a system's behavior rather than just verify it. You can step through transitions manually, evaluate expressions in the current state, test hypotheses about guards, and trace variable changes across history.

```bash
tla MyProtocol.tla -c 'Users={"u1","u2"}' -c 'Resources={"r1"}' --allow-deadlock -i
```

Key bindings: arrow keys to select actions, Enter to take an action, `b` to backtrack, `e` for the REPL, `t` for variable trace, `h` for hypothesis testing, `g` to show guard conditions. When an action has many changes, Right arrow or Space expands the details.

Interactive mode is especially useful for understanding counterexample traces. After a model check finds a violation, replay the trace interactively to see exactly what went wrong at each step.

## Scenarios

Drive the checker along a specific execution path using TLA+ predicates:

```bash
tla MyProtocol.tla -c 'Users={"u1","u2"}' -c 'Resources={"r1"}' --allow-deadlock \
  --scenario "step: state'[\"u1\"] = \"active\"
step: owner'[\"r1\"] = \"u1\"
step: state'[\"u2\"] = \"active\""
```

Each `step:` line is a TLA+ expression over current (unprimed) and next-state (primed) variables. The checker finds a transition matching each predicate in sequence. An `action:` line pins the step to a named action instead, optionally constrained by an expression after a `;`:

```
action: Start
action: Claim; owner'["r1"] = "u1"
action: Release
```

Put the lines in a file and pass `--scenario @path.txt`. Use this to validate that a specific path exists in your model — "can we actually reach the state we think we can?" — or to set up a specific scenario before switching to free exploration.

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
| Sensitivity analysis | `--sweep 'Param=V1;V2;V3' --count-satisfying InvName --continue` |
| Explore interactively | `-i` |
| Verify specific path exists | `--scenario @path.txt` |
| Quick iteration during development | `--quick` |
| Reduce symmetric state space | `--symmetry ConstName` |
| Machine-readable output | `--json` |
| Visualize state graph | `--export-dot graph.dot` |
| Check liveness/fairness | `--check-liveness` |
| Use the liveness engine before 0.16 | `--liveness-engine legacy` |
| Use a cfg file other than `Spec.cfg` | `--config path.cfg` |
| Treat `Nat`/`Int` as infinite sets | `--symbolic-integers` |
| Check that the spec refines an instance | `--check-refinement ALIAS` |
| Treat variables an action leaves unassigned as unchanged | `--allow-unassigned-stutter` |

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

The excerpts above are simplified from [`test_cases/should_pass/pingpong.tla`](test_cases/should_pass/pingpong.tla) and [`MChannel.tla`](test_cases/should_pass/MChannel.tla) (which add a ping counter, type checks and `Assert`s); with two clients and two pings the complete spec explores 17 states:

```bash
tla test_cases/should_pass/pingpong.tla -c NumberOfClients=2 -c NumberOfPings=2 --allow-deadlock
```

## Stack Size

Expression evaluation grows its own stack as needed, so deep recursion in a spec does not need any setting (a `RECURSIVE` operator 50,000 calls deep runs on the default stack). Parsing does not: an expression nested about a thousand levels deep (such as 1,000 nested parentheses) overflows the default 8 MB stack on macOS. `RUST_MIN_STACK` does not help, since it applies only to threads the program spawns. Raise the shell's stack limit before running instead:

```bash
ulimit -s 65520
tla spec.tla ...
```

65520 KB is the hard limit on macOS; `ulimit -Hs` shows the limit on your system.
