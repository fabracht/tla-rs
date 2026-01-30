# Feedback on MQDB TLA+ Bug Report

## Bug Triage Results

Three bugs were reported from the TLA+ model checking. Here's what happened with each.

### Bug 1: MQDBOutbox InvNoDoubleDelivery — FIXED

The outbox double delivery bug was real and has been fixed in MQDB commit `62402bd`.

The TLA+ spec (`MQDBOutbox.tla`) correctly identified the issue: `DispatchEventFailure` resets `dispatch_idx` to 0 without recording progress, so the next `StartDispatch` re-dispatches from event 1, duplicating events that already succeeded.

The report noted this was "latent" because `dispatcher.dispatch()` always returns `Ok(())` in practice. That assessment was reasonable given current code, but dispatch can fail in real deployments (network errors during cross-node forwarding, subscriber disconnects during QoS 1 delivery). The bug was worth fixing.

**What we changed in `src/outbox.rs`:**
- Added `dispatched_count: usize` to `StoredOutboxEntry` (with `#[serde(default)]` for backward compat)
- New method `update_dispatched_count(op_id, count)` persists progress + increments retry in one write
- `process_pending()` now skips already-dispatched events via `.skip(entry.dispatched_count)` and tracks progress during iteration
- On partial failure: calls `update_dispatched_count` instead of `increment_retry`
- On full success: `mark_delivered` as before (no extra writes on happy path)

This maps directly to adding `dispatch_idx` tracking to the `OutboxEntry` in the TLA+ model — the spec showed exactly what the fix needed to look like.

### Bug 2: MQDBAsyncReplication InvAckedDataDurable — BY DESIGN

Correct assessment. MQDB uses fire-and-forget async replication (`replicate_write_async`). There's no quorum tracking on individual writes. Durability comes from the replication factor and partition reassignment on node failure, not from write-time acknowledgment. The TLA+ invariant was modeling a stronger guarantee than the system provides.

### Bug 3: MQDBOutboxBugNoAtomicity InvDataImpliesOutboxOrDelivered — ALREADY MITIGATED

Correct. The real code uses `BatchWriter` to atomically commit data + outbox entry in a single transaction. The spec confirmed why this pattern matters — without atomicity, you get data records with no corresponding outbox entry, meaning change events are silently lost. The existing implementation already handles this correctly.

## Quality of the Specs

The `MQDBOutbox.tla` spec is well-structured. Modeling `dispatch_idx` as an explicit variable that steps through events one at a time made the double-delivery visible immediately in the counterexample trace. The separation of `DispatchEventSuccess` and `DispatchEventFailure` as distinct actions cleanly captures the partial failure scenario.

The `InvNoDoubleDelivery` invariant (`\A key \in EventKey : delivery_count[key] <= 1`) is the right property. It caught a genuine bug that unit tests didn't cover.

One observation: the spec's `DispatchEventFailure` doesn't model partial progress at all — it just resets. This is accurate to the original code, which is why the bug exists. A follow-up spec could add `dispatched_count` to the `OutboxEntry` record and verify the fix eliminates the counterexample.

## Suggestion for Next Spec Iteration

If you want to verify the fix formally, modify `MQDBOutbox.tla` to add `dispatched_count` to `OutboxEntry` and update `DispatchEventFailure` to persist `dispatch_idx` into `dispatched_count` before resetting. Then `StartDispatch` should initialize `dispatch_idx` from `entry.dispatched_count + 1` instead of `1`. The `InvNoDoubleDelivery` invariant should hold with this change.

## Real Bug 1: Double Delivery on Consumer Timeout — DOES NOT APPLY

The `MQDBDelivery.tla` spec models a Kafka-style pull-based consumer group where consumers claim events for delivery, timeout causes requeue to another consumer, and the original consumer completes delivery — producing a double delivery.

MQDB doesn't work this way. It uses push-and-forget dispatch:

1. `OutboxProcessor::process_pending()` calls `dispatcher.dispatch(event)` (outbox.rs:262)
2. `dispatch()` fires into a channel and returns `Ok(())` (dispatcher.rs:41-101)
3. Event is immediately marked delivered via `mark_delivered()` (outbox.rs:287)
4. Consumer timeout (`remove_stale_members` in consumer_group.rs:152-172) only removes the member and rebalances — there is no requeue of inflight messages
5. Events are broadcast via MQTT topics (`$DB/{entity}/events/{id}`) in agent.rs:367-404

There is no delivery claim, no requeue mechanism, no way for two consumers to receive the same outbox event. The TLA+ spec modeled an architecture that doesn't match the implementation.

## Real Bug 2: Stale Epoch Write — ALREADY FENCED

The `MQDBCluster.tla` spec models a scenario where a partitioned primary completes a local write after failover. MQDB has fencing at three layers:

1. **Role check**: `is_local_partition()` (node_controller.rs:204-211) checks `ReplicaRole::Primary` before accepting writes
2. **Step-down**: `PartitionUpdate` handler (node_controller.rs:680-717) calls `step_down()` when node is not in the assignment, changing role to `None`
3. **Replica rejection**: `handle_write()` (replication.rs:102-104) returns `StaleEpoch` for writes with outdated epoch

A stale primary that receives a `PartitionUpdate` after failover steps down and can no longer write. If it somehow sends a stale write to replicas, it's rejected by epoch comparison.

## All Real Bugs — Final Status

| Bug | Source | Disposition |
|-----|--------|-------------|
| Outbox Double Delivery on Failure | `MQDBOutbox.tla` | **FIXED** (commit `62402bd`) |
| Double Delivery on Consumer Timeout | `MQDBDelivery.tla` | **DOES NOT APPLY** (architecture mismatch) |
| Stale Epoch Write | `MQDBCluster.tla` | **ALREADY FENCED** (3-layer epoch protection) |
