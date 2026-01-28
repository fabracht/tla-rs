# MQDB TLA+ Specification Diary

## 2026-01-27 — Initial Specs + First Verification

### What We Built

Four self-contained TLA+ specs modeling MQDB's critical systems:

- **MQDBCore.tla** — Single-node CRUD, event dispatch, outbox with retry/dead-letter
- **MQDBConstraints.tla** — Unique and not-null constraint enforcement
- **MQDBConsumerGroup.tla** — Consumer group join/leave with partition assignment
- **MQDBCluster.tla** — Multi-node partition ownership, replication, quorum commit

All four parse and model-check under tlc-executor with small constant domains.

### Verification Results

Cross-checked every spec against MQDB source code. Findings grouped by severity.

#### Correct

- Event sequence monotonicity (AtomicU64 + SeqCst fetch_add)
- Outbox entry structure, retry_count starting at 0, dead-letter threshold
- Delivery removes from outbox via mark_delivered
- Not-null enforcement on create and update
- Unique constraint validation excludes self on update
- Join/leave triggers immediate rebalance
- Partition assignment covers all partitions when members exist
- Quorum formula equivalent to peers.len().div_ceil(2) + 1
- Per-partition epoch with monotonic increment on promotion
- Stale epoch rejection on replication
- Sequence gap buffering with max_pending_gap
- Raft manages topology, custom protocol handles data replication

#### Mismatches

1. **Cascade delete produces multiple events** — MQDBCore models Delete as emitting one event. Real code emits 1 + N cascade events grouped under one operation_id. The outbox stores a Vec<ChangeEvent>, not a single event.

2. **Null vs absent field semantics** — MQDBConstraints treats null as "skip unique validation". Real code skips when the field is absent from the JSON object. An explicit `{"field": null}` still triggers unique index lookup.

3. **Epoch initialization** — MQDBCluster initializes epochs to 1. Real code uses Epoch::ZERO (0-based). Functionally equivalent but semantically different.

#### Omissions (Known, Intentional)

These were scoped out in the plan's "What NOT to Model" section:

- MQTT/QUIC transport details
- TLS/auth/ACL
- Schema type validation details
- TTL cleanup, dedup store
- Cursor/pagination
- Raft leader election protocol details

#### Omissions (Discovered, Should Address)

1. **Foreign key constraints** — MQDBConstraints only models Unique and NotNull. The real system has ForeignKeyConstraint with Restrict/Cascade/SetNull on-delete semantics. Cascade delete is recursive with cycle detection via visited set. This is the biggest gap.

2. **Heartbeat timeout** — MQDBConsumerGroup models explicit join/leave but not timeout-based stale member removal. Real code has consumer_timeout_ms (default 30s) with a background task running every timeout/2 that evicts stale members and triggers rebalance.

3. **NotReplica ack status** — MQDBCluster models StaleEpoch and SequenceGap but not the NotReplica rejection. Real code rejects writes to nodes not yet in replica role (pre-initialization phase).

4. **Catchup retry mechanism** — MQDBCluster models gap detection but not the proactive catchup request protocol (5-second interval, CATCHUP_REQUEST_INTERVAL_MS).

5. **Multi-field unique constraints** — MQDBConstraints models single-field uniqueness. Real code supports composite unique keys across multiple fields.

6. **Rebalance determinism** — MQDBConsumerGroup uses nondeterministic CHOOSE for partition assignment. Real code sorts consumer IDs and assigns round-robin (partition % len). The spec is an over-approximation — invariants hold but we can't verify load-balance properties.

7. **Operation ID grouping** — MQDBCore doesn't model operation_id. Real code groups multiple events (especially cascade deletes) under one operation_id for atomic delivery.

### What to Work on Next

Priority order based on impact:

1. **Add FK constraints to MQDBConstraints.tla** — Model ForeignKeyConstraint with on_delete actions. Restrict prevents deletion when references exist. Cascade recursively deletes dependents. SetNull nullifies referencing fields. Needs cycle detection. This is the largest gap between spec and code.

2. **Fix cascade delete in MQDBCore.tla** — Delete should produce 1+ events. Model operation_id to group events atomically. Outbox entry should hold event count or list.

3. **Add heartbeat timeout to MQDBConsumerGroup.tla** — Model a clock variable. Add HeartbeatTimeout action that removes stale members and triggers rebalance. Needed for liveness properties.

4. **Fix null vs absent semantics in MQDBConstraints.tla** — Distinguish between "field is null" and "field is absent" in unique validation. Real code only skips absent fields.

5. **Add NotReplica handling to MQDBCluster.tla** — Model replica role state (None/Primary/Replica). Reject writes to nodes with role=None.

6. **Add catchup protocol to MQDBCluster.tla** — Model catchup request/response for sequence gaps beyond buffering threshold.

### tlc-executor Issues Found

During development we hit an evaluator bug: nested `~\E` quantifiers inside `\A` bodies within function definitions cause `UndefinedVar` errors during next-state candidate inference. The evaluator's `collect_candidates` traversal doesn't properly handle deeply nested quantifier bindings when expanding through function definitions.

**Workaround**: Extract inner quantifier logic into separate named definitions. Example: use `UniqueOk(data, uf)` instead of inlining `~\E oid \in Ids : ...` inside a forall body.

Also discovered that all four MQDB specs require RUST_MIN_STACK=33554432 (32MB) due to deep recursion in eval from nested function access patterns like `store[id][field]`.

### Test Configuration

Constants used for model checking (kept small for tractable state spaces):

| Spec | Constants | Notes |
|------|-----------|-------|
| MQDBCore | Ids={"id1"}, Values={"v1"}, MaxRetries=2, MaxSeq=3 | MaxSeq bounds event counter |
| MQDBConstraints | Ids={"id1"}, Fields={"name"}, FieldValues={"a"} | Single field keeps state space small |
| MQDBConsumerGroup | Consumers={"c1","c2"}, Groups={"g1"}, Partitions={0,1} | 2 consumers, 2 partitions |
| MQDBCluster | Nodes={"n1","n2"}, Partitions={0}, MaxSeq=1 | Slowest spec (~45s at 500 states) |
