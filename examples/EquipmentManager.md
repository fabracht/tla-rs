# Equipment Manager TLA+ Specification Explained

## Overview

This specification models how the Equipment Manager agent fetches options (license data) for hardware modules from AWS IoT. It captures:

- **Permanent metadata subscription** - Agent listens for metadata changes while equipment is active
- **Ephemeral data subscription** - Agent subscribes to data only when needed, then unsubscribes
- **Network timing issues** - Data and metadata can arrive at the broker at different times
- **Timestamp validation** - Only accept data matching the metadata timestamp

---

## 1. Module Header

```tla
---- MODULE EquipmentManager ----
EXTENDS Naturals, Sequences, FiniteSets
```

- Names the module "EquipmentManager"
- Imports standard libraries for numbers, sequences (lists), and set operations

---

## 2. Constants (Configuration)

```tla
CONSTANTS Serials, MaxTimestamp
```

Values provided when running the model checker:

| Constant | Example | Meaning |
|----------|---------|---------|
| `Serials` | `{"s1", "s2"}` | Set of equipment serial numbers |
| `MaxTimestamp` | `2` | Highest version/timestamp number to explore |

---

## 3. Variables (System State)

```tla
VARIABLES
    taskQueue,          \* Worker queue for background tasks
    activeSerials,      \* Set of registered serial numbers (= subscribed to metadata)
    metadataAtBroker,   \* Timestamp of metadata retained at MQTT broker
    dataAtBroker,       \* Timestamp of data retained at MQTT broker
    receivedMetadata,   \* Timestamp of metadata agent has received
    cachedTimestamp,    \* Timestamp of successfully cached options
    subscribedToData,   \* Is agent subscribed to data topic? (ephemeral)
    metadataTimerActive,\* Is 60-second timer running?
    requestSent         \* Has explicit request been sent to cloud?
```

### Key Insight: Two Types of Subscriptions

| Subscription | Variable | Lifetime |
|--------------|----------|----------|
| **Metadata** | `activeSerials` membership | Permanent while equipment connected |
| **Data** | `subscribedToData[s]` | Temporary, only during fetch |

When `s ∈ activeSerials`, the agent is subscribed to the metadata topic for serial `s`. This subscription lasts until the equipment is removed.

When `subscribedToData[s] = TRUE`, the agent has temporarily subscribed to the data topic to fetch options. This subscription ends after matching data is received.

### State Example

```
activeSerials = {"s1"}                        \* s1 registered, subscribed to its metadata topic
subscribedToData = ("s1" :> TRUE @@ "s2" :> FALSE)  \* Also temporarily subscribed to s1's data topic
metadataAtBroker = ("s1" :> 2 @@ "s2" :> 0)   \* Broker has metadata ts=2 for s1
dataAtBroker = ("s1" :> 2 @@ "s2" :> 0)       \* Broker has data ts=2 for s1
receivedMetadata = ("s1" :> 2 @@ "s2" :> 0)   \* Agent received metadata ts=2
cachedTimestamp = ("s1" :> 0 @@ "s2" :> 0)    \* Waiting for matching data
```

---

## 4. Helper Definitions

```tla
Timestamps == 1..MaxTimestamp
TaskMeta(s) == <<"meta", s>>
```

- `Timestamps` - Valid version numbers: `{1, 2, ..., MaxTimestamp}`
- `TaskMeta(s)` - Creates a task tuple like `<<"meta", "s1">>`

---

## 5. Initial State

```tla
Init ==
    /\ taskQueue = <<>>
    /\ activeSerials = {}
    /\ metadataAtBroker = [s \in Serials |-> 0]
    /\ dataAtBroker = [s \in Serials |-> 0]
    /\ receivedMetadata = [s \in Serials |-> 0]
    /\ cachedTimestamp = [s \in Serials |-> 0]
    /\ subscribedToData = [s \in Serials |-> FALSE]
    /\ metadataTimerActive = [s \in Serials |-> FALSE]
    /\ requestSent = [s \in Serials |-> FALSE]
```

**In plain English:**

> The system starts with:
> - No tasks queued
> - No equipment registered (no metadata subscriptions)
> - Nothing at the broker (timestamp 0 = empty)
> - Agent has received nothing, cached nothing
> - No data topic subscriptions
> - No timers, no pending requests

---

## 6. Actions (State Transitions)

### ManifestUpdate(s) — Equipment Registers

```tla
ManifestUpdate(s) ==
    /\ s \notin activeSerials
    /\ activeSerials' = activeSerials \union {s}
    /\ metadataTimerActive' = [metadataTimerActive EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<taskQueue, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, requestSent>>
```

**When:** Equipment with serial `s` is not already registered.

**What happens:**
1. Add `s` to active serials (this means: subscribe to metadata topic)
2. Start the 60-second timer

**Real system:** Hardware module inserted → manifest published to local MQTT → agent detects it → subscribes to cloud metadata topic `equipment/{s}/options/information/metadata/v1` → starts timer waiting for retained metadata.

**Important:** The metadata subscription created here persists until equipment removal.

---

### CloudPublishesData(s) — Cloud Publishes New Data

```tla
CloudPublishesData(s) ==
    /\ \E ts \in Timestamps:
        /\ ts > dataAtBroker[s]
        /\ ts > metadataAtBroker[s]
        /\ dataAtBroker' = [dataAtBroker EXCEPT ![s] = ts]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>
```

**When:** A new timestamp `ts` is being published, newer than current data and metadata.

**What happens:** Data with timestamp `ts` arrives at the broker's retained storage.

**Real system:** Cloud backend publishes options data to `equipment/{s}/options/information/data/v1` with `retain=true`. Data is published FIRST.

---

### CloudPublishesMetadata(s) — Cloud Publishes Metadata

```tla
CloudPublishesMetadata(s) ==
    /\ dataAtBroker[s] > metadataAtBroker[s]
    /\ metadataAtBroker' = [metadataAtBroker EXCEPT ![s] = dataAtBroker[s]]
    /\ UNCHANGED <<taskQueue, activeSerials, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>
```

**When:** Data at broker is newer than metadata (data was published, metadata not yet).

**What happens:** Metadata is published, matching the data timestamp.

**Real system:** Cloud publishes metadata to `equipment/{s}/options/information/metadata/v1` with `retain=true`. Metadata is published SECOND — it's the "flag" that signals data is ready.

---

### ReceiveMetadata(s) — Agent Receives New Metadata

```tla
ReceiveMetadata(s) ==
    /\ s \in activeSerials
    /\ metadataAtBroker[s] > 0
    /\ metadataAtBroker[s] > receivedMetadata[s]
    /\ metadataAtBroker[s] > cachedTimestamp[s]
    /\ receivedMetadata' = [receivedMetadata EXCEPT ![s] = metadataAtBroker[s]]
    /\ metadataTimerActive' = [metadataTimerActive EXCEPT ![s] = FALSE]
    /\ subscribedToData' = [subscribedToData EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, dataAtBroker,
                   cachedTimestamp, requestSent>>
```

**When:**
- `s ∈ activeSerials` — Equipment is registered (agent is subscribed to metadata)
- Metadata exists at broker
- Metadata is newer than what we've seen
- Metadata is newer than our cache

**What happens:**
1. Record the metadata timestamp
2. Stop the 60-second timer
3. Subscribe to the data topic (ephemeral subscription starts)

**Real system:** Because agent is subscribed to metadata topic, it receives the retained message. Compares timestamp with cache. If newer version available, subscribes to data topic to fetch it.

**Note:** The agent was already subscribed to metadata (via `activeSerials`). This action represents the retained message being delivered, not a new subscription.

---

### ReceiveDataMatching(s) — Agent Receives Correct Data

```tla
ReceiveDataMatching(s) ==
    /\ s \in activeSerials
    /\ subscribedToData[s] = TRUE
    /\ dataAtBroker[s] = receivedMetadata[s]
    /\ receivedMetadata[s] > cachedTimestamp[s]
    /\ cachedTimestamp' = [cachedTimestamp EXCEPT ![s] = receivedMetadata[s]]
    /\ subscribedToData' = [subscribedToData EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, dataAtBroker,
                   receivedMetadata, metadataTimerActive, requestSent>>
```

**When:**
- Equipment is registered
- Agent is subscribed to data topic (ephemeral)
- **Data timestamp equals metadata timestamp** — they match!
- This is newer than our cache

**What happens:**
1. Update cache to the new timestamp
2. Unsubscribe from data topic (ephemeral subscription ends)

**Real system:** Agent receives retained data, validates timestamp matches metadata, decrypts and saves to cache, publishes to local MQTT for hardware, unsubscribes from data topic.

**Important:** Agent remains subscribed to metadata topic (still in `activeSerials`). Only the data subscription ends.

---

### ReceiveDataStale(s) — Agent Receives Old Data

```tla
ReceiveDataStale(s) ==
    /\ s \in activeSerials
    /\ subscribedToData[s] = TRUE
    /\ dataAtBroker[s] < receivedMetadata[s]
    /\ UNCHANGED vars
```

**When:**
- Equipment is registered
- Agent is subscribed to data topic
- **Data timestamp is OLDER than metadata timestamp** — stale!

**What happens:** Nothing. Agent ignores the stale data and keeps waiting.

**Real system:** Due to network lag, broker might still have old data retained. Agent logs warning, stays subscribed to data topic, waits for correct version to arrive.

**This is the key race condition:** Metadata says "version 2 ready" but broker still has version 1 data.

---

### MetadataTimeout(s) — 60-Second Timer Fires

```tla
MetadataTimeout(s) ==
    /\ s \in activeSerials
    /\ metadataTimerActive[s] = TRUE
    /\ metadataAtBroker[s] = 0
    /\ requestSent[s] = FALSE
    /\ taskQueue' = Append(taskQueue, TaskMeta(s))
    /\ requestSent' = [requestSent EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<activeSerials, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive>>
```

**When:**
- Equipment is registered
- Timer is running
- No metadata at broker (nothing retained)
- Haven't sent a request yet

**What happens:**
1. Queue a metadata request task for the worker
2. Mark request as sent

**Real system:** 60 seconds passed, no retained metadata received. This means the cloud has no data for this equipment yet. Agent sends explicit request to `equipment/{s}/options/information/request/v1` to trigger cloud to populate the topics.

---

### ProcessTask — Worker Processes Queue

```tla
ProcessTask ==
    /\ Len(taskQueue) > 0
    /\ taskQueue' = Tail(taskQueue)
    /\ UNCHANGED <<activeSerials, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>
```

**When:** Queue has tasks.

**What happens:** Dequeue and process the first task.

**Real system:** Worker thread picks up task, sends MQTT request to cloud.

---

## 7. Next State Relation

```tla
Next ==
    \/ \E s \in Serials: ManifestUpdate(s)
    \/ \E s \in Serials: CloudPublishesData(s)
    \/ \E s \in Serials: CloudPublishesMetadata(s)
    \/ \E s \in Serials: ReceiveMetadata(s)
    \/ \E s \in Serials: ReceiveDataMatching(s)
    \/ \E s \in Serials: ReceiveDataStale(s)
    \/ \E s \in Serials: MetadataTimeout(s)
    \/ ProcessTask
```

**In plain English:**

> Each step, the system does ONE of these (non-deterministic choice):
> - Equipment registers (starts metadata subscription + timer)
> - Cloud publishes data to broker
> - Cloud publishes metadata to broker
> - Agent receives metadata (already subscribed, gets retained message)
> - Agent receives matching data (validates, caches, ends data subscription)
> - Agent receives stale data (ignores it)
> - Timer fires (queue explicit request)
> - Worker processes a task

---

## 8. Invariants (Safety Properties)

### InvDataSubRequiresMetadata

```tla
InvDataSubRequiresMetadata ==
    \A s \in Serials:
        subscribedToData[s] => (receivedMetadata[s] > cachedTimestamp[s])
```

> Data subscription only exists when we have metadata newer than our cache.

Enforces the two-stage protocol.

---

### InvCacheNotNewerThanReceived

```tla
InvCacheNotNewerThanReceived ==
    \A s \in Serials:
        cachedTimestamp[s] <= receivedMetadata[s]
```

> We only cache what we have metadata for.

---

### InvReceivedNotNewerThanBroker

```tla
InvReceivedNotNewerThanBroker ==
    \A s \in Serials:
        receivedMetadata[s] <= metadataAtBroker[s]
```

> Agent can't receive metadata that doesn't exist at broker.

---

### InvMetadataNotNewerThanData

```tla
InvMetadataNotNewerThanData ==
    \A s \in Serials:
        metadataAtBroker[s] <= dataAtBroker[s]
```

> Metadata at broker is never newer than data (data published first).

---

### InvDataSubOnlyWhenActive / InvTimersOnlyWhenActive

```tla
InvDataSubOnlyWhenActive ==
    \A s \in Serials:
        subscribedToData[s] => (s \in activeSerials)

InvTimersOnlyWhenActive ==
    \A s \in Serials:
        metadataTimerActive[s] => (s \in activeSerials)
```

> Data subscriptions and timers only exist for registered equipment.

---

## 9. Fairness

```tla
Fairness ==
    /\ WF_vars(ProcessTask)
    /\ \A s \in Serials: WF_vars(MetadataTimeout(s))
    /\ \A s \in Serials: WF_vars(ReceiveMetadata(s))
    /\ \A s \in Serials: WF_vars(ReceiveDataMatching(s))
    /\ \A s \in Serials: WF_vars(CloudPublishesData(s))
    /\ \A s \in Serials: WF_vars(CloudPublishesMetadata(s))
```

`WF` (Weak Fairness) means: "If continuously enabled, must eventually happen."

This prevents unrealistic scenarios like "cloud never publishes" or "agent never receives."

---

## 10. Liveness Property

```tla
OptionsEventuallyArrive ==
    \A s \in Serials:
        (s \in activeSerials /\ receivedMetadata[s] > 0) ~>
        (cachedTimestamp[s] = receivedMetadata[s])
```

**In plain English:**

> For all serials: If equipment is registered AND metadata was received, EVENTUALLY the cache will have matching data.

This guarantees: **registered equipment eventually gets its options.**

---

## 11. Visual Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           EQUIPMENT LIFECYCLE                               │
└─────────────────────────────────────────────────────────────────────────────┘

1. REGISTRATION
   ┌──────────────────────────────────────────────────────────────────────────┐
   │  ManifestUpdate(s)                                                       │
   │                                                                          │
   │  • Hardware inserted, manifest published                                 │
   │  • Agent subscribes to metadata topic (PERMANENT)                        │
   │  • 60-second timer starts                                                │
   │                                                                          │
   │  activeSerials = {"s1"}     ←── s1 now subscribed to metadata           │
   │  metadataTimerActive[s1] = TRUE                                          │
   └──────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
2. WAITING FOR METADATA (agent is subscribed, waiting for retained message)
                                      │
            ┌─────────────────────────┴─────────────────────────┐
            │                                                   │
            ▼                                                   ▼
   ┌─────────────────────┐                         ┌─────────────────────────┐
   │ Retained metadata   │                         │ No retained metadata    │
   │ arrives             │                         │ (60s timer fires)       │
   │                     │                         │                         │
   │ ReceiveMetadata(s)  │                         │ MetadataTimeout(s)      │
   │ • Record timestamp  │                         │ • Queue explicit request│
   │ • Stop timer        │                         │ • Cloud will publish    │
   │ • Subscribe to DATA │                         └────────────┬────────────┘
   └──────────┬──────────┘                                      │
              │                                                 │
              │ subscribedToData[s1] = TRUE                     │
              │ (ephemeral subscription)                        │
              │                                                 │
              ▼                                                 │
3. WAITING FOR DATA                                             │
              │                                                 │
    ┌─────────┴─────────┐                                       │
    │                   │                                       │
    ▼                   ▼                                       │
┌─────────────┐   ┌──────────────┐                              │
│ Data ts     │   │ Data ts      │                              │
│ matches     │   │ is OLDER     │                              │
│ metadata    │   │ (stale)      │                              │
│             │   │              │                              │
│ReceiveData  │   │ReceiveData   │                              │
│ Matching(s) │   │ Stale(s)     │                              │
│             │   │              │                              │
│ • Cache it! │   │ • Ignore     │                              │
│ • Unsub     │   │ • Keep       │                              │
│   from DATA │   │   waiting    │──────┐                       │
└──────┬──────┘   └──────────────┘      │                       │
       │                                │                       │
       │ subscribedToData[s1] = FALSE   │                       │
       │ (ephemeral sub ended)          │                       │
       │                                │                       │
       │ BUT STILL IN activeSerials     │                       │
       │ (metadata sub continues)       │                       │
       ▼                                ▼                       │
4. OPTIONS CACHED ◄─────────────────────────────────────────────┘
   (still listening for future metadata updates)
```

---

## 12. Subscription Summary

| Event | Metadata Subscription | Data Subscription |
|-------|----------------------|-------------------|
| Equipment registers | **STARTS** | - |
| Metadata received (new version) | continues | **STARTS** |
| Data received (matching) | continues | **ENDS** |
| Data received (stale) | continues | continues (waiting) |
| Equipment removed | **ENDS** | ends (if active) |

The metadata subscription is tied to `activeSerials` membership — it's the "always listening" channel. The data subscription is explicit (`subscribedToData`) — it's the "fetch this specific version" channel.

---

## 13. Test Commands

```bash
# Safety check
cargo run -- examples/EquipmentManager.tla \
  -c 'Serials={"s1"}' -c 'MaxTimestamp=2' --allow-deadlock

# Safety + Liveness
cargo run -- examples/EquipmentManager.tla \
  -c 'Serials={"s1"}' -c 'MaxTimestamp=2' --allow-deadlock --check-liveness
```
