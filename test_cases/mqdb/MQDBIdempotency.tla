---- MODULE MQDBIdempotency ----
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Entities, MaxRequests

VARIABLES
    store,
    request_count,
    proceed_count

vars == <<store, request_count, proceed_count>>

Status == {"processing", "committed"}

Init ==
    /\ store = [k \in {} |-> [status |-> "processing", entity |-> "", response |-> ""]]
    /\ request_count = 0
    /\ proceed_count = [k \in Keys |-> 0]

TypeOK ==
    /\ DOMAIN store \subseteq Keys
    /\ \A k \in DOMAIN store :
        /\ store[k].status \in Status
        /\ store[k].entity \in Entities
    /\ request_count <= MaxRequests * 3
    /\ \A k \in Keys : proceed_count[k] >= 0

NewRequest(key, entity) ==
    /\ request_count < MaxRequests
    /\ key \notin DOMAIN store
    /\ proceed_count[key] = 0
    /\ store' = [k \in (DOMAIN store \cup {key}) |->
        IF k = key
        THEN [status |-> "processing", entity |-> entity, response |-> ""]
        ELSE store[k]]
    /\ request_count' = request_count + 1
    /\ proceed_count' = [proceed_count EXCEPT ![key] = @ + 1]

RetryWhileProcessing(key, entity) ==
    /\ request_count < MaxRequests * 3
    /\ key \in DOMAIN store
    /\ store[key].status = "processing"
    /\ store[key].entity = entity
    /\ request_count' = request_count + 1
    /\ UNCHANGED <<store, proceed_count>>

RetryAfterCommitted(key, entity) ==
    /\ request_count < MaxRequests * 3
    /\ key \in DOMAIN store
    /\ store[key].status = "committed"
    /\ store[key].entity = entity
    /\ request_count' = request_count + 1
    /\ UNCHANGED <<store, proceed_count>>

ParameterMismatch(key, entity) ==
    /\ request_count < MaxRequests * 3
    /\ key \in DOMAIN store
    /\ store[key].entity # entity
    /\ request_count' = request_count + 1
    /\ UNCHANGED <<store, proceed_count>>

CommitRequest(key) ==
    /\ key \in DOMAIN store
    /\ store[key].status = "processing"
    /\ store' = [store EXCEPT ![key] = [@ EXCEPT !.status = "committed", !.response = "ok"]]
    /\ UNCHANGED <<request_count, proceed_count>>

AbortRequest(key) ==
    /\ key \in DOMAIN store
    /\ store[key].status = "processing"
    /\ store' = [k \in (DOMAIN store \ {key}) |-> store[k]]
    /\ UNCHANGED <<request_count, proceed_count>>

ExpireRecord(key) ==
    /\ key \in DOMAIN store
    /\ store[key].status = "committed"
    /\ store' = [k \in (DOMAIN store \ {key}) |-> store[k]]
    /\ UNCHANGED <<request_count, proceed_count>>

Next ==
    \/ \E k \in Keys, e \in Entities : NewRequest(k, e)
    \/ \E k \in Keys, e \in Entities : RetryWhileProcessing(k, e)
    \/ \E k \in Keys, e \in Entities : RetryAfterCommitted(k, e)
    \/ \E k \in Keys, e \in Entities : ParameterMismatch(k, e)
    \/ \E k \in Keys : CommitRequest(k)
    \/ \E k \in Keys : AbortRequest(k)
    \/ \E k \in Keys : ExpireRecord(k)

InvNoDoubleProcessing ==
    \A k \in DOMAIN store :
        store[k].status = "processing" => proceed_count[k] = 1

InvCommittedHasResponse ==
    \A k \in DOMAIN store :
        store[k].status = "committed" => store[k].response # ""

InvExactlyOnceSemantics ==
    \A k \in Keys : proceed_count[k] <= 1

====
