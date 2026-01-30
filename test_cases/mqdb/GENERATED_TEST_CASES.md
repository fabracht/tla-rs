# MQDB Generated Test Cases

Test cases generated from TLA+ model checking counterexamples. Each test case represents a bug scenario that was caught by an invariant violation.

---

# REAL BUGS DISCOVERED

These bugs were found by model checking the **correct** spec with invariants that represent safety properties. They represent actual implementation flaws that could occur in production.

---

## REAL BUG 1: Double Delivery on Timeout

**Bug**: When a consumer times out while processing an event, the event is requeued for another consumer. But the original consumer may complete delivery anyway, resulting in the same event being delivered twice.

**Invariant Violated**: `InvNoDoubleDelivery` - each event must be delivered by at most one consumer

**Source**: `MQDBDelivery.tla`

### Scenario

```
Consumers = {"c1", "c2"}, Partitions = {0}, MaxEvents = 2

Step 0: Initial state
  members = {}
  outbox = {}
  inflight = {}
  delivered = {}

Step 1-2: Produce events 0 and 1
  outbox = {0, 1}

Step 3: c1 joins (gets partition 0)
  members = {"c1"}
  assignments = {0: "c1"}

Step 4: c1 starts delivery of event 1
  outbox = {0}
  inflight = {<<1, "c1">>}

Step 5: c1 times out (leaves group, event requeued)
  members = {}
  outbox = {0, 1}            ← Event 1 back in outbox
  inflight = {<<1, "c1">>}   ← But still "in flight" for c1!

Step 6: c1 completes delivery (doesn't know it timed out)
  delivered = {<<1, "c1">>}  ← First delivery

Step 7: c2 joins (gets partition 0)
  members = {"c2"}
  assignments = {0: "c2"}

Step 8: c2 starts delivery of event 1
  inflight = {<<1, "c2">>}

Step 9: c2 completes delivery
  delivered = {<<1, "c1">>, <<1, "c2">>}  ← DOUBLE DELIVERY!
```

### Root Cause

The consumer's local delivery process is not coordinated with the broker's timeout detection. When the broker decides a consumer has timed out:
1. It requeues the event for another consumer
2. But the original consumer's in-flight processing continues
3. Both consumers complete delivery

### Fix Required

1. **Generation/fencing tokens**: Include a generation number in delivery claims; check generation before acknowledging completion
2. **Lease-based delivery**: Consumer must renew lease while processing; broker rejects ack if lease expired
3. **Exactly-once delivery tracking**: Track delivery by event ID globally, not per-consumer

### Test Implementation

```rust
#[test]
fn test_double_delivery_on_timeout() {
    let mut broker = Broker::new();
    broker.add_partition(0);

    let c1 = broker.join_consumer("c1");
    broker.produce_event(Event { id: 1, partition: 0 });

    // c1 starts processing
    let delivery = c1.start_delivery(1);
    assert!(delivery.is_ok());

    // Simulate timeout - broker thinks c1 is dead
    broker.timeout_consumer("c1");

    // c2 joins and gets the requeued event
    let c2 = broker.join_consumer("c2");
    let delivery2 = c2.start_delivery(1);

    // c1 completes (unaware of timeout)
    let ack1 = c1.complete_delivery(1);

    // c2 completes
    let ack2 = c2.complete_delivery(1);

    // At least one should fail (the fix)
    assert!(
        ack1.is_err() || ack2.is_err(),
        "Both deliveries succeeded - double delivery bug!"
    );
}
```

---

## REAL BUG 2: Stale Epoch Write

**Bug**: A primary node starts a write, fails (from the cluster's perspective), but its write completes locally. Meanwhile, a new primary is elected. The stale write from the old epoch is now in the system, violating linearizability.

**Invariant Violated**: `InvNoStaleEpochWrite` - writes should only exist at the current epoch

**Source**: `MQDBCluster.tla`

### Scenario

```
Nodes = {"n1", "n2"}, Partitions = {0}, MaxSeq = 2

Step 0: Initial state
  primary = {0: "n1"}
  epoch = {0: 1}
  alive = {"n1": true, "n2": true}
  inflight_writes = {}
  write_epochs = {"n1": {0: 0}, "n2": {0: 0}}

Step 1: n1 starts a write at epoch 1
  inflight_writes = {<<"n1", 0, 1>>}

Step 2: n1 fails (network partition)
  alive = {"n1": false, "n2": true}
  inflight_writes = {<<"n1", 0, 1>>}  ← Still in flight!

Step 3: n1's write completes (n1 doesn't know it's "dead")
  seq = {"n1": {0: 1}, "n2": {0: 0}}
  write_epochs = {"n1": {0: 1}, ...}  ← Write at epoch 1

Step 4: n2 promoted to primary at epoch 2
  primary = {0: "n2"}
  epoch = {0: 2}
  write_epochs = {"n1": {0: 1}, ...}  ← STALE WRITE AT EPOCH 1!
```

### Root Cause

The cluster's failure detection is asynchronous with the node's local operations:
1. Node starts write, captures current epoch
2. Failure detector marks node as dead
3. New primary elected, epoch increments
4. Old node's write completes (locally) without epoch validation
5. System now has writes from two different epochs

### Fix Required

1. **Epoch fencing**: Include epoch in write requests; replicas reject writes with stale epochs
2. **Lease-based primary**: Primary must hold valid lease to write; lease invalidated on failover
3. **Quorum-based epoch validation**: Write only commits if quorum confirms epoch is current

### Test Implementation

```rust
#[test]
fn test_stale_epoch_write_rejected() {
    let mut cluster = Cluster::new(vec!["n1", "n2"]);
    cluster.elect_primary("n1", partition: 0);

    // n1 starts a write at epoch 1
    let write_handle = cluster.node("n1").start_write(partition: 0, data: "value1");
    let write_epoch = cluster.epoch(partition: 0);  // 1

    // Simulate n1 failure and failover to n2
    cluster.mark_failed("n1");
    cluster.elect_primary("n2", partition: 0);
    assert_eq!(cluster.epoch(partition: 0), 2);

    // n1's write tries to complete
    let result = write_handle.complete();

    // Should be rejected due to stale epoch
    assert!(
        result.is_err(),
        "Stale epoch write accepted - split-brain bug!"
    );
    assert_eq!(
        result.unwrap_err().kind(),
        ErrorKind::StaleEpoch { expected: 2, got: write_epoch }
    );
}
```

---

## Test Case 1: Retry Bypass (Unbounded Retries)

**Bug**: Event retry allowed even after max retries exhausted
**Invariant Violated**: `InvRetryBounded` - retries should never exceed MaxRetries
**Source**: `bugs/MQDBCore_BugRetryBypass.tla`

### Scenario
```
MaxRetries = 2

Step 0: Initial state
  store = {"id1": nil}
  outbox = {}

Step 1: Create("id1", "v1")
  store = {"id1": "v1"}
  outbox = [{seq: 0, op: "create", retries: 0}]

Step 2: RetryEvent(seq=0)
  outbox = [{seq: 0, op: "create", retries: 1}]

Step 3: RetryEvent(seq=0)
  outbox = [{seq: 0, op: "create", retries: 2}]

Step 4: RetryEvent(seq=0)  ← BUG: Should be blocked!
  outbox = [{seq: 0, op: "create", retries: 3}]  ← Exceeds MaxRetries
```

### Test Implementation
```rust
#[test]
fn test_retry_respects_max_retries() {
    let mut core = MQDBCore::new(max_retries: 2);
    core.create("id1", "v1");

    core.retry_event(0);  // retries = 1
    core.retry_event(0);  // retries = 2

    // This should fail or move to dead letter, not increment
    assert!(core.retry_event(0).is_err() || core.is_dead_lettered(0));
}
```

---

## Test Case 2: Lost Event (Silent Drop)

**Bug**: Event removed from outbox without delivery or dead-letter tracking
**Invariant Violated**: `InvEventNotLost` - every created event must be in outbox, delivered, or dead-lettered
**Source**: `bugs/MQDBCore_BugLostEvent.tla`

### Scenario
```
Step 0: Initial state
  store = {"id1": nil}
  outbox = {}
  delivered = {}
  dead_letter = {}

Step 1: Create("id1", "v1")
  store = {"id1": "v1"}
  outbox = [{seq: 0, op: "create", retries: 0}]
  event_seq = 1

Step 2: DropEvent(seq=0)  ← BUG: Silent drop!
  outbox = {}
  delivered = {}      ← Event 0 not here
  dead_letter = {}    ← Event 0 not here either
  event_seq = 1       ← But event 0 was created!
```

### Test Implementation
```rust
#[test]
fn test_events_never_lost() {
    let mut core = MQDBCore::new();
    core.create("id1", "v1");
    let event_seq = core.last_event_seq();  // 0

    // Simulate internal error that removes from outbox
    core.internal_remove_from_outbox(event_seq);

    // Event must still be trackable
    assert!(
        core.is_in_outbox(event_seq) ||
        core.is_delivered(event_seq) ||
        core.is_dead_lettered(event_seq)
    );
}
```

---

## Test Case 3: Double Create (Overwrite)

**Bug**: Create allowed on existing record without checking existence
**Invariant Violated**: `InvNoOverwrite` - cannot have multiple pending create events
**Source**: `bugs/MQDBCore_BugDoubleCreate.tla`

### Scenario
```
Step 0: Initial state
  store = {"id1": nil}
  outbox = {}

Step 1: Create("id1", "v1")
  store = {"id1": "v1"}
  outbox = [{seq: 0, op: "create", retries: 0}]

Step 2: Create("id1", "v1")  ← BUG: Should be blocked!
  store = {"id1": "v1"}       (value overwritten, same in this case)
  outbox = [
    {seq: 0, op: "create", retries: 0},
    {seq: 1, op: "create", retries: 0}  ← Two creates!
  ]
```

### Test Implementation
```rust
#[test]
fn test_create_requires_not_exists() {
    let mut core = MQDBCore::new();
    core.create("id1", "v1");

    // Second create on same ID should fail
    let result = core.create("id1", "v2");
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind(), ErrorKind::AlreadyExists);
}
```

---

## Test Case 4: Orphan Partition (Missing Rebalance)

**Bug**: Consumer joins but partitions not reassigned
**Invariant Violated**: `InvAllPartitionsAssigned` - when members exist, all partitions must be assigned
**Source**: `bugs/MQDBConsumerGroup_BugOrphanPartition.tla`

### Scenario
```
Partitions = {0, 1}

Step 0: Initial state
  members["g1"] = {}
  assignments["g1"] = {0: "none", 1: "none"}

Step 1: Join("c1", "g1")
  members["g1"] = {"c1"}
  assignments["g1"] = {0: "none", 1: "none"}  ← BUG: Still unassigned!
```

### Test Implementation
```rust
#[test]
fn test_join_triggers_rebalance() {
    let mut group = ConsumerGroup::new("g1", partitions: vec![0, 1]);

    group.join("c1");

    // All partitions should be assigned to c1
    assert_eq!(group.assignment(0), Some("c1"));
    assert_eq!(group.assignment(1), Some("c1"));
}

#[test]
fn test_leave_triggers_rebalance() {
    let mut group = ConsumerGroup::new("g1", partitions: vec![0, 1]);
    group.join("c1");
    group.join("c2");

    group.leave("c1");

    // All partitions should be reassigned to c2
    for p in [0, 1] {
        assert_eq!(group.assignment(p), Some("c2"));
    }
}
```

---

## Summary

### Real Bugs (found via model checking correct specs)

| Bug | Type | Component | Invariant | Counterexample |
|-----|------|-----------|-----------|----------------|
| Double Delivery on Timeout | Race condition | Consumer Groups | `InvNoDoubleDelivery` | `bugs/double_delivery.json` |
| Stale Epoch Write | Split-brain | Cluster | `InvNoStaleEpochWrite` | `bugs/stale_epoch_write.json` |
| Outbox Double Delivery on Failure | Partial failure retry | Outbox | `InvNoDoubleDelivery` | See MQDBOutbox.tla |

**Outbox Double Delivery — FIXED** (MQDB commit `62402bd`). `MQDBOutbox.tla` found the bug: `DispatchEventFailure` resets `dispatch_idx` to 0 without recording progress, so retries re-deliver already-dispatched events. `MQDBOutboxNoFailure.tla` confirmed removing the failure path eliminates the bug. `MQDBOutboxFixed.tla` models the fix (adding `dispatched_count` to `OutboxEntry` so retries resume from last successful event) and verifies `InvNoDoubleDelivery` holds across 10,356 states with failures enabled (3 ops, 3 events, 3 retries).

### Artificial Bugs (specs modified to introduce bugs for demonstration)

| Test Case | Bug Type | Component | Key Assertion |
|-----------|----------|-----------|---------------|
| Retry Bypass | Missing guard | Outbox | `retries <= max_retries` |
| Lost Event | Silent failure | Outbox | `event ∈ outbox ∪ delivered ∪ dead_letter` |
| Double Create | Missing check | Store | `!exists(id) before create` |
| Orphan Partition | Missing action | ConsumerGroup | `members ≠ {} ⇒ all partitions assigned` |

---

## Reproducing Real Bugs

```bash
# Double delivery on timeout
cargo run --release -- test_cases/mqdb/MQDBDelivery.tla \
  --constant 'Consumers={"c1","c2"}' --constant 'Partitions={0}' \
  --constant 'MaxEvents=2' \
  --allow-deadlock --save-counterexample bugs/double_delivery.json

# Stale epoch write
cargo run --release -- test_cases/mqdb/MQDBCluster.tla \
  --constant 'Nodes={"n1","n2"}' --constant 'Partitions={0}' \
  --constant 'MaxSeq=2' \
  --allow-deadlock --save-counterexample bugs/stale_epoch_write.json
```

---

## Reproducing Artificial Bugs

Generate counterexamples:
```bash
# Retry bypass
cargo run -- test_cases/mqdb/bugs/MQDBCore_BugRetryBypass.tla \
  --constant 'Ids={"id1"}' --constant 'Values={"v1"}' \
  --constant 'MaxRetries=2' --constant 'MaxSeq=5' \
  --allow-deadlock --save-counterexample bug.json

# Lost event
cargo run -- test_cases/mqdb/bugs/MQDBCore_BugLostEvent.tla \
  --constant 'Ids={"id1"}' --constant 'Values={"v1"}' \
  --constant 'MaxRetries=2' --constant 'MaxSeq=3' \
  --allow-deadlock --save-counterexample bug.json

# Double create
cargo run -- test_cases/mqdb/bugs/MQDBCore_BugDoubleCreate.tla \
  --constant 'Ids={"id1"}' --constant 'Values={"v1","v2"}' \
  --constant 'MaxRetries=1' --constant 'MaxSeq=4' \
  --allow-deadlock --save-counterexample bug.json

# Orphan partition
cargo run -- test_cases/mqdb/bugs/MQDBConsumerGroup_BugOrphanPartition.tla \
  --constant 'Consumers={"c1"}' --constant 'Groups={"g1"}' \
  --constant 'Partitions={0,1}' \
  --allow-deadlock --save-counterexample bug.json
```
