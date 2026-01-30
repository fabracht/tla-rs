# Interactive Tool Improvements

Based on the sync routing bug hunt experience, these features would significantly improve the debugging workflow.

## Priority 1: Guard Visibility

### Problem
When stepping through a trace or exploring interactively, it's unclear WHY an action was enabled or disabled.

### Current State
```
Available Actions:
  [1] ReceiveMutation
  [2] ReceiveState
  [3] Subscribe
```

### Proposed Improvement
```
Available Actions:
  [1] ReceiveMutation(c="a", d="d1", seq=1)
      ✓ <<d1,1>> ∈ inflight[a]
      ✓ d1 ∈ awaiting_state[a] → will buffer

  [2] ReceiveState(c="a", d="d1")
      ✓ d1 ∈ awaiting_state[a]
      snapshot_seq would be: 1
      buffered to apply: {}

  [3] Subscribe(c="b", d="d1")
      ✓ d1 ∉ subscribed[b]
```

### Implementation
1. After computing `next_states()`, also compute guard bindings
2. For each enabled action, evaluate sub-expressions and store
3. Display guard status in action list

## Priority 2: Invariant Failure Explanation

### Problem
When an invariant fails, we see the full state but not WHY it failed.

### Current State
```
Invariant InvConsistency violated!
State 7:
  client_seq = (a :> (d1 :> 1) @@ b :> (d1 :> 2))
  server_seq = (d1 :> 2)
  ...
```

### Proposed Improvement
```
Invariant InvConsistency violated!

InvConsistency ==
  ∀ c ∈ Clients, d ∈ Diagrams:
    Synced(c, d) ⟹ client_seq[c][d] = server_seq[d]

FAILED for c="a", d="d1":

  Synced("a", "d1") = TRUE
    ✓ d1 ∈ subscribed[a] = {d1}
    ✓ d1 ∉ awaiting_state[a] = {}
    ✓ no inflight for (a, d1)

  But: client_seq[a][d1] = 1
       server_seq[d1] = 2

  1 = 2 → FALSE ✗
```

### Implementation
1. When invariant fails, find the first failing binding (c, d, etc.)
2. Evaluate each conjunct separately with that binding
3. Display the evaluation tree with values

## Priority 3: Variable History ("trace" command)

### Problem
Understanding "how did this variable get this value?" requires manually reading through states.

### Proposed Feature
```
> trace client_seq[a][d1]

History of client_seq[a][d1]:
  State 0: -1 (initial)
  State 3: 0  (ReceiveState: snapshot_seq=0)
  State 5: 1  (ReceiveMutation: seq=1)
  State 7: 1  (unchanged - but server_seq became 2!)

> trace server_seq[d1]

History of server_seq[d1]:
  State 0: 0 (initial)
  State 4: 1 (Mutate by b)
  State 6: 2 (Mutate by b)
```

### Implementation
1. During exploration, record which action changed which variables
2. Store `(state_idx, var_path, old_value, new_value, action)` tuples
3. On `trace` command, filter and display history

## Priority 4: Hypothesis Testing

### Problem
After finding a bug, testing "would this fix work?" requires editing the spec and re-running.

### Proposed Feature
```
> hypothesis add-guard ReceiveMutation "seq > client_seq[c][d]"

Testing hypothesis against current trace...

State 5 → 6: ReceiveMutation(a, d1, 1)
  New guard: 1 > client_seq[a][d1]
           = 1 > 1
           = FALSE

  Action would be BLOCKED with this guard!

Hypothesis result: Would prevent reaching State 7 (the violation)
```

### Implementation
1. Parse guard expression
2. For each state transition in the trace, re-evaluate with added guard
3. Report first transition that would be blocked

## Priority 5: "What Changed?" Diff Mode

### Current State
State diffs show `(was: ...)` but for complex nested structures it's hard to see.

### Proposed Improvement
```
State 5 → 6 via Mutate(b, d1):

  CHANGED:
    server_seq[d1]: 1 → 2
    client_seq[b][d1]: 1 → 2  (author self-update)
    inflight[a]: {} → {<<d1, 2>>}

  UNCHANGED (but relevant):
    client_seq[a][d1]: 1
    awaiting_state[a]: {}
```

### Implementation
1. Compute deep diff between states
2. Group by "changed" vs "unchanged but referenced by action"
3. Color-code additions/removals

## Priority 6: Counterexample Replay Mode

### Problem
Static counterexample output is hard to understand. Want to step through interactively.

### Proposed Feature
```
$ tlc-executor spec.tla --replay counterexample.json

Loaded counterexample with 8 states.

[State 0/7] Initial
  Press 'n' for next, 'p' for previous, 'g N' to go to state N

> n

[State 1/7] via SubscribeAction
  Changed: subscribed[a] = {} → {d1}
           awaiting_state[a] = {} → {d1}

> g 7

[State 7/7] VIOLATION
  InvConsistency failed for c=a, d=d1

> trace client_seq[a][d1]
...
```

### Implementation
1. Save counterexample as JSON during checking
2. Load and display in interactive mode
3. Allow navigation, trace queries, hypothesis testing

---

## Implementation Order

1. **Guard Visibility** - Most immediately useful, helps understand "why did this happen?"
2. **Invariant Failure Explanation** - Critical for debugging, currently a pain point
3. **Variable History** - Enables "how did we get here?" reasoning
4. **Counterexample Replay** - Combines all features for post-hoc analysis
5. **Hypothesis Testing** - Nice to have, speeds up fix iteration
6. **Diff Mode** - Polish, improves readability

---

## Data Structures Needed

```rust
// For guard visibility
struct ActionWithGuards {
    action: Transition,
    guard_evaluations: Vec<GuardEval>,
}

struct GuardEval {
    expression: String,      // "d ∈ subscribed[c]"
    value: bool,
    subexpressions: Vec<(String, Value)>,  // [("d", "d1"), ("subscribed[c]", {"d1"})]
}

// For variable history
struct VarChange {
    state_idx: usize,
    var_path: String,        // "client_seq[a][d1]"
    old_value: Value,
    new_value: Value,
    action: Option<String>,  // "Mutate(b, d1)"
}

// For counterexample replay
struct Counterexample {
    states: Vec<State>,
    actions: Vec<Option<String>>,
    var_changes: Vec<Vec<VarChange>>,  // per transition
    violation: Option<InvariantViolation>,
}
```
