---- MODULE MQDBOwnership_BugAgentSkip ----
EXTENDS Naturals, FiniteSets

CONSTANTS Users, Entities, OwnedEntities, Nodes

ASSUME OwnedEntities \subseteq Entities

VARIABLES phase, sender, entity, mode, activeFilters, queryLog

vars == <<phase, sender, entity, mode, activeFilters, queryLog>>

OwnerFilter(u) == [field |-> "userId", value |-> u]

Init ==
    /\ phase = "idle"
    /\ sender = "none"
    /\ entity = "none"
    /\ mode = "none"
    /\ activeFilters = {}
    /\ queryLog = {}

Receive ==
    /\ phase = "idle"
    /\ \E u \in Users, e \in Entities, m \in {"agent", "cluster"}, target \in Users \union {"none"}:
        /\ sender' = u
        /\ entity' = e
        /\ mode' = m
        /\ activeFilters' = IF target = "none" THEN {} ELSE {OwnerFilter(target)}
        /\ phase' = "received"
        /\ UNCHANGED queryLog

InjectOwnerFilter ==
    /\ phase = "received"
    /\ entity \in OwnedEntities
    /\ mode = "cluster"
    /\ activeFilters' = activeFilters \union {OwnerFilter(sender)}
    /\ phase' = "filtered"
    /\ UNCHANGED <<sender, entity, mode, queryLog>>

SkipInjection ==
    /\ phase = "received"
    /\ \/ entity \notin OwnedEntities
       \/ (entity \in OwnedEntities /\ mode = "agent")
    /\ phase' = "filtered"
    /\ UNCHANGED <<sender, entity, mode, activeFilters, queryLog>>

AgentExecute ==
    /\ phase = "filtered"
    /\ mode = "agent"
    /\ queryLog' = queryLog \union {[sender |-> sender, entity |-> entity, filters |-> activeFilters, node |-> "local"]}
    /\ phase' = "done"
    /\ UNCHANGED <<sender, entity, mode, activeFilters>>

ClusterExecute ==
    /\ phase = "filtered"
    /\ mode = "cluster"
    /\ queryLog' = queryLog \union {[sender |-> sender, entity |-> entity, filters |-> activeFilters, node |-> n] : n \in Nodes}
    /\ phase' = "done"
    /\ UNCHANGED <<sender, entity, mode, activeFilters>>

Next ==
    \/ Receive
    \/ InjectOwnerFilter
    \/ SkipInjection
    \/ AgentExecute
    \/ ClusterExecute

Spec == Init /\ [][Next]_vars

InvOwnershipEnforced ==
    \A q \in queryLog:
        q.entity \in OwnedEntities => OwnerFilter(q.sender) \in q.filters

TypeOK ==
    /\ phase \in {"idle", "received", "filtered", "done"}
    /\ sender \in Users \union {"none"}
    /\ entity \in Entities \union {"none"}
    /\ mode \in {"agent", "cluster", "none"}

====
