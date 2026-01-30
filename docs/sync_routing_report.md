# Sync Routing Design Report

## Problem Statement

Design a pub/sub routing system where:
- Multiple browser clients connect to a sync server
- Clients edit diagrams and send mutations
- Server routes mutations only to clients subscribed to that diagram
- No client should receive mutations for diagrams they don't care about

## Formal Verification Results

We used TLA+ model checking to verify the design.

### Bug Found: Stale Pending on Unsubscribe

**Naive implementation violates safety.**

Counterexample:
```
1. Client B subscribes to diagram D
2. Client A subscribes to diagram D
3. Client A mutates D → Server queues mutation for B
4. Client B unsubscribes from D → BUG: mutation still queued!
5. Server delivers mutation to B for diagram B doesn't care about
```

**Fix**: When client unsubscribes, clear their pending queue for that diagram.

### Liveness Analysis

| Property | Result | Meaning |
|----------|--------|---------|
| "Pending → Eventually Delivered" | ❌ VIOLATED | Mutations can be starved |
| "Pending → Eventually Cleared" | ✅ PASSES | Pending always resolves |

**Key insight**: Pending can be cleared by unsubscribe OR delivery. The property "mutations are delivered" cannot be guaranteed even with strong fairness, because unsubscribe provides an escape hatch.

**Verdict**: This is acceptable. If user unsubscribes, they explicitly don't want mutations for that diagram.

### MQTT Semantics Warning

Initial assumption was wrong. MQTT spec says:
- Broker **MUST complete** in-flight QoS 1/2 messages after unsubscribe
- Broker only stops **adding new** messages

**Implication**: Application layer must handle receiving messages after unsubscribe.

---

## Recommended Algorithm

### Data Structures

```rust
// Server-side state
struct SyncServer {
    // Which clients are subscribed to which diagrams
    subscriptions: HashMap<DiagramId, HashSet<ClientId>>,

    // Pending mutations per client (for reliable delivery)
    pending: HashMap<ClientId, HashMap<DiagramId, Vec<Mutation>>>,

    // Client connections
    clients: HashMap<ClientId, WebSocketConnection>,
}
```

### Core Operations

#### 1. Subscribe

```rust
fn subscribe(client_id: ClientId, diagram_id: DiagramId) {
    self.subscriptions
        .entry(diagram_id)
        .or_default()
        .insert(client_id);

    // Send current diagram state to client (initial sync)
    self.send_full_state(client_id, diagram_id);
}
```

#### 2. Unsubscribe (CRITICAL - includes the fix)

```rust
fn unsubscribe(client_id: ClientId, diagram_id: DiagramId) {
    // Remove from subscription set
    if let Some(subscribers) = self.subscriptions.get_mut(&diagram_id) {
        subscribers.remove(&client_id);
    }

    // CRITICAL: Clear pending mutations for this diagram
    if let Some(client_pending) = self.pending.get_mut(&client_id) {
        client_pending.remove(&diagram_id);
    }
}
```

#### 3. Handle Mutation

```rust
fn handle_mutation(author_id: ClientId, diagram_id: DiagramId, mutation: Mutation) {
    // Persist to database first
    self.db.apply_mutation(&diagram_id, &mutation);

    // Route to subscribers (excluding author)
    if let Some(subscribers) = self.subscriptions.get(&diagram_id) {
        for client_id in subscribers {
            if *client_id != author_id {
                self.queue_and_send(client_id, diagram_id, mutation.clone());
            }
        }
    }
}

fn queue_and_send(client_id: &ClientId, diagram_id: DiagramId, mutation: Mutation) {
    // Add to pending queue
    self.pending
        .entry(client_id.clone())
        .or_default()
        .entry(diagram_id)
        .or_default()
        .push(mutation.clone());

    // Attempt delivery
    self.try_deliver(client_id, diagram_id);
}
```

#### 4. Handle Client Disconnect

**Decision Point**: What happens to subscriptions and pending on disconnect?

| Option | On Disconnect | On Reconnect | Tradeoff |
|--------|---------------|--------------|----------|
| **A: Clean Slate** | Clear subs + pending | Client re-subscribes, gets full state | Simple, no stale data |
| **B: Preserve All** | Keep subs + pending | Resume delivery where left off | Complex, reliable |
| **C: Preserve Intent** | Keep subs, clear pending | Resume subscriptions, get full state | Middle ground |

**Recommendation: Option A (Clean Slate)** for simplicity.

```rust
fn handle_disconnect(client_id: ClientId) {
    // Remove from all subscription sets
    for subscribers in self.subscriptions.values_mut() {
        subscribers.remove(&client_id);
    }

    // Clear all pending
    self.pending.remove(&client_id);

    // Close connection
    self.clients.remove(&client_id);
}
```

#### 5. Handle Client Reconnect

```rust
fn handle_reconnect(client_id: ClientId, connection: WebSocketConnection) {
    // Store new connection
    self.clients.insert(client_id.clone(), connection);

    // Client must re-subscribe to diagrams they want
    // This triggers send_full_state() for each, ensuring consistency
}
```

**Why Clean Slate is preferred:**

1. **Consistency**: Client gets fresh state, no missing mutations
2. **Simplicity**: No need to track "last seen" sequence numbers
3. **Verified safe**: TLA+ model `sync_reconnect_clear.tla` passes (64 states)

**When to use Option B (Preserve All):**

- Mutations are expensive to regenerate
- Network is flaky (frequent short disconnects)
- You need exactly-once delivery semantics

If using Option B, you must also track sequence numbers to detect gaps.

---

## Initial State Sync (Second Bug Found)

### Problem: Race Between Subscribe and State Fetch

When using MQTT with separate `$DB/` protocol for state fetching:

```
Timeline:
─────────────────────────────────────────────────────────────────────
Client A                    Server                    Client B
─────────────────────────────────────────────────────────────────────
subscribe(D)
                                                      mutate(D) → seq=5
                            queues mutation for A
request $DB/list/nodes
                            reads state (includes seq=5)
receives mutation seq=5
                            responds with state
receives state response
applies state (has seq=5)
applies buffered mutation   ← BUG: DOUBLE-APPLY or STATE REGRESSION!
─────────────────────────────────────────────────────────────────────
```

### Counterexample from TLA+

Model checking found this violation with 2 clients, 1 diagram, MaxSeq=2:

```
State 5: B receives state response (snapshot_seq=1), client_applied_seq[B]=1
         BUT B still has inflight mutation (d1, 1) not yet delivered
State 6: B mutates → client_applied_seq[B]=2 (author updates own state)
State 7: B receives OLD mutation (d1, 1) → client_applied_seq[B]=1
         BUG: Overwrote seq=2 with seq=1!
```

### Fix: Sequence Number Filtering

**Server must include sequence numbers. Client must filter.**

```typescript
// Server state
diagram_seq: Map<DiagramId, number>  // monotonic per diagram

// On mutation
diagram_seq[d]++
publish({ seq: diagram_seq[d], mutation: ... })

// On $DB/list response
return { up_to_seq: diagram_seq[d], entities: [...] }
```

```typescript
// Client state
client_applied_seq: Map<DiagramId, number>

// On receive mutation (when NOT awaiting state)
function handleMutation(diagramId: string, seq: number, mutation: Mutation) {
    // CRITICAL: Only apply if seq > current applied seq
    if (seq > this.client_applied_seq.get(diagramId)) {
        this.applyMutation(diagramId, mutation);
        this.client_applied_seq.set(diagramId, seq);
    }
    // else: mutation already incorporated, ignore
}

// On receive state response
function handleStateResponse(diagramId: string, state: DiagramState, upToSeq: number) {
    this.applyFullState(diagramId, state);
    this.client_applied_seq.set(diagramId, upToSeq);

    // Apply buffered mutations that are newer than snapshot
    for (const { seq, mutation } of this.buffered.get(diagramId)) {
        if (seq > upToSeq) {
            this.applyMutation(diagramId, mutation);
            this.client_applied_seq.set(diagramId, seq);
        }
    }
    this.buffered.delete(diagramId);
}
```

### Verified Safe

TLA+ model `sync_initial_state.tla` with the fix passes with 4656 states (3 clients, 3 max seq).

---

### Client-Side Defense

Even with server-side fix, client should defensively ignore unexpected mutations:

```typescript
function handleMutation(diagramId: string, mutation: Mutation) {
    // Defense: ignore mutations for diagrams we're not subscribed to
    if (!this.subscriptions.has(diagramId)) {
        console.warn(`Ignoring mutation for unsubscribed diagram: ${diagramId}`);
        return;
    }

    this.applyMutation(diagramId, mutation);
}
```

---

## Protocol Messages

### Client → Server

```typescript
// Subscribe to diagram updates
{ type: "subscribe", diagram_id: string }

// Unsubscribe from diagram updates
{ type: "unsubscribe", diagram_id: string }

// Send mutation
{ type: "mutation", diagram_id: string, mutation: Mutation }

// Acknowledge received mutation (for reliable delivery)
{ type: "ack", mutation_id: string }
```

### Server → Client

```typescript
// Full diagram state (on subscribe)
{ type: "state", diagram_id: string, state: DiagramState }

// Incremental mutation
{ type: "mutation", diagram_id: string, mutation_id: string, mutation: Mutation }

// Subscription confirmed
{ type: "subscribed", diagram_id: string }

// Unsubscription confirmed
{ type: "unsubscribed", diagram_id: string }
```

---

## MQTT Alternative

If using MQTT instead of raw WebSocket:

```
Topic structure:
    diagrams/{diagram_id}/mutations

Subscribe:
    client.subscribe(`diagrams/${diagramId}/mutations`)

Unsubscribe:
    client.unsubscribe(`diagrams/${diagramId}/mutations`)

Publish mutation:
    client.publish(`diagrams/${diagramId}/mutations`, mutation)
```

**Warning**: With MQTT QoS 1/2, client may receive messages after unsubscribe. Client-side filtering is required.

---

## Invariants to Maintain

These must hold at all times:

1. **No stale pending**: `∀ client, diagram: pending[client][diagram] ≠ ∅ ⟹ diagram ∈ subscriptions[client]`

2. **Author exclusion**: Mutation author never receives their own mutation

3. **Complete routing**: All subscribers (except author) receive the mutation

---

## Testing Checklist

1. [ ] Basic routing: A mutates, B receives (both subscribed)
2. [ ] Author exclusion: A mutates, A does NOT receive
3. [ ] Non-subscriber exclusion: A mutates D1, B (subscribed to D2 only) does NOT receive
4. [ ] Unsubscribe clears pending: A has pending, A unsubscribes, pending cleared
5. [ ] Race condition: Mutation in-flight when unsubscribe arrives
6. [ ] Reconnection: Client disconnects with pending, reconnects
7. [ ] Multiple diagrams: Client subscribed to D1 and D2, receives correct routing
8. [ ] Initial sync race: B subscribes, A mutates, B receives state + late mutation
9. [ ] Sequence filtering: B ignores mutation with seq ≤ client_applied_seq
10. [ ] Buffered mutations: B buffers mutations while awaiting state, applies seq > snapshot

---

## Files Reference

| File | Purpose | Result |
|------|---------|--------|
| `test_cases/sync_routing2.tla` | Naive spec (buggy) | ❌ Safety violated |
| `test_cases/sync_routing_fixed.tla` | Fixed spec | ✅ Safety verified |
| `test_cases/sync_leads_to.tla` | Liveness without fairness | ❌ Violated |
| `test_cases/sync_with_fairness.tla` | Liveness with weak fairness | ❌ Violated |
| `test_cases/sync_strong_fairness.tla` | Liveness with strong fairness | ❌ Violated |
| `test_cases/sync_pending_cleared.tla` | "Pending cleared" property | ✅ Passes |
| `test_cases/sync_reconnect.tla` | Reconnect Option B (keep pending) | ✅ 144 states |
| `test_cases/sync_reconnect_clear.tla` | Reconnect Option A (clean slate) | ✅ 64 states |
| `test_cases/sync_initial_state_buggy.tla` | Initial sync without seq filter (buggy) | ❌ Safety violated |
| `test_cases/sync_initial_state.tla` | Initial sync with seq filter | ✅ 4656 states |

---

## Summary

**Two bugs found by model checking:**

1. **Bug #1: Stale pending on unsubscribe**
   - Fix: Clear pending queue when client unsubscribes

2. **Bug #2: State regression during initial sync**
   - Fix: Filter mutations by sequence number (`seq > client_applied_seq`)

**Design principles:**

1. **Use explicit subscription model** - clients tell server what they care about
2. **Clear pending on unsubscribe** - critical fix from Bug #1
3. **Use sequence numbers** - critical fix from Bug #2
4. **Client-side filtering** - defense in depth, especially with MQTT
5. **Accept liveness limitation** - mutations may be cleared by unsubscribe instead of delivery, which is fine semantically
