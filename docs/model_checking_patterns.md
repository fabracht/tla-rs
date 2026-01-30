# Model Checking Patterns and Lessons Learned

Patterns discovered while using tlc-executor for distributed systems verification.

## Pattern 1: Define "Steady State" Predicates

**Problem**: Invariants like `client_state = server_state` fail during transient states (messages in flight, awaiting responses).

**Solution**: Define a predicate that captures "the system has settled":

```tla
Synced(client, resource) ==
    /\ resource \in subscribed[client]           \* client cares about it
    /\ resource \notin awaiting_response[client] \* not waiting for data
    /\ ~\E m \in inflight[client]: m.resource = resource  \* no pending messages
```

Then write invariants as implications:
```tla
InvConsistency == \A c, r: Synced(c, r) => client_state[c][r] = server_state[r]
```

## Pattern 2: Model Messages as Sets, Not Queues

**Why**: Real networks can reorder, duplicate, or delay messages. Modeling as sets captures this non-determinism without requiring explicit reordering actions.

```tla
\* Good: Set of pending messages (any order)
inflight == [client \in Clients |-> SUBSET Message]

\* Receive any pending message
Receive(c, m) ==
    /\ m \in inflight[c]
    /\ inflight' = [inflight EXCEPT ![c] = @ \ {m}]
```

**When to use queues**: Only when the protocol guarantees ordering (TCP, sequence numbers).

## Pattern 3: Sequence Numbers for Distributed State

**Problem found**: State snapshots and incremental updates can race. Client receives:
1. Snapshot at seq=5
2. Late update seq=3 (already in snapshot)
3. Applying update overwrites correct state!

**Solution**: Always filter by sequence number:

```tla
ReceiveUpdate(c, resource, seq, data) ==
    /\ seq > client_applied_seq[c][resource]  \* CRITICAL: only apply if newer
    /\ client_state' = [client_state EXCEPT ![c][resource] = Apply(data)]
    /\ client_applied_seq' = [client_applied_seq EXCEPT ![c][resource] = seq]
```

## Pattern 4: Separate "Requesting" from "Subscribed"

**Problem found**: Client subscribes, requests initial state, receives mutations while waiting. Need to buffer mutations and apply after state arrives.

**Solution**: Track subscription phases:

```tla
VARIABLES
    subscribed,      \* {resource} - what client wants
    awaiting_state,  \* {resource} - waiting for initial state
    buffered         \* [resource |-> {seq}] - mutations received while waiting
```

State machine per resource:
```
not_subscribed → awaiting_state → subscribed (steady state)
                     ↓
              buffer mutations
```

## Pattern 5: Clear Pending on Unsubscribe

**Problem found**: Client unsubscribes while mutations are queued. Server later delivers mutation for resource client doesn't care about.

**Solution**: Unsubscribe must atomically clear pending:

```tla
Unsubscribe(c, r) ==
    /\ subscribed' = [subscribed EXCEPT ![c] = @ \ {r}]
    /\ pending' = [pending EXCEPT ![c] = @ \ {m \in @ : m.resource = r}]  \* CRITICAL
```

## Pattern 6: Incremental Spec Development

**Process that worked**:

1. **Start minimal**: 2 clients, 1 resource, simple actions
2. **Find first bug**: Usually in the "obvious" action
3. **Fix and re-verify**: Ensure fix doesn't break other properties
4. **Add complexity**: More clients, reconnection, initial sync
5. **Find deeper bugs**: Interactions between features

Each spec should answer ONE question. Don't try to model everything at once.

## Pattern 7: Read Counterexamples Carefully

**Red flags in traces**:

1. **Multiple variables changing unexpectedly**: If an action should only change X but Y also changed, something is wrong with the spec OR the action attribution
2. **State "going backward"**: seq=2 becoming seq=1 indicates missing guard
3. **Impossible guards satisfied**: If an action fires when its guard shouldn't be true, check the guard logic

**Technique**: For each transition, mentally verify:
- Which action could have caused this?
- Are all changes consistent with that action?
- Why was this action enabled?

## Pattern 8: Author Self-Updates

**Problem found**: When client A mutates, A's local state must also update. Otherwise A falls behind.

```tla
Mutate(author, resource) ==
    /\ server_state' = [server_state EXCEPT ![resource] = Apply(mutation)]
    /\ server_seq' = [server_seq EXCEPT ![resource] = @ + 1]
    \* CRITICAL: Author updates own state immediately
    /\ client_state' = [client_state EXCEPT ![author][resource] = Apply(mutation)]
    /\ client_seq' = [client_seq EXCEPT ![author][resource] = server_seq[resource] + 1]
    \* Route to OTHER clients
    /\ pending' = [c \in Clients |-> IF c /= author /\ ... THEN ...]
```

## Anti-Pattern: Trusting "Obviously Correct" Code

Both bugs found were in "simple" actions:
- `Unsubscribe`: "Just remove from set" - forgot to clear pending
- `ReceiveMutation`: "Just apply it" - forgot to check sequence

**Lesson**: The simpler the action looks, the more likely you missed an edge case. Model check it anyway.

---

## Interactive Tool Wishlist

Based on this experience, features that would help:

### Show Guard Evaluation
After each action, show which guards were checked and their values:
```
ReceiveMutation(b, d1, 1) fired because:
  ✓ <<d1, 1>> ∈ inflight[b] = TRUE
  ✓ d1 ∉ awaiting_state[b] = TRUE  (so: direct apply mode)
  ✗ 1 > client_seq[b][d1] = FALSE  ← would have blocked if guard existed!
```

### Highlight Invariant Failure
When invariant fails, show the specific binding that failed:
```
InvConsistency failed:
  For c="b", r="d1":
    Synced(b, d1) = TRUE
    client_state[b][d1] = 1
    server_state[d1] = 2
    Expected: 1 = 2 → FALSE
```

### Trace Backward From Failure
"How did this variable get this value?"
```
> trace client_seq[b][d1]

State 7: 1 (set by ReceiveMutation)
State 6: 2 (set by Mutate, author=b)
State 5: 1 (set by ReceiveState)
State 4: -1 (initial)
```

### Hypothesis Testing
"Would this guard have prevented the bug?"
```
> hypothesis: add "seq > client_seq[c][d]" to ReceiveMutation

Testing hypothesis against counterexample...
State 6→7 transition would be BLOCKED
  ReceiveMutation(b, d1, 1): guard fails (1 > 2 = FALSE)

Hypothesis would prevent this bug!
```
