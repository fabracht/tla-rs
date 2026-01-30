---- MODULE MQDBAsyncReplication_BugDurabilityLoss ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWrites

VARIABLES
    primary,
    alive,
    node_data,
    client_acks,
    epoch

vars == <<primary, alive, node_data, client_acks, epoch>>

Quorum == (Cardinality(Nodes) / 2) + 1

Init ==
    /\ primary \in Nodes
    /\ alive = [n \in Nodes |-> TRUE]
    /\ node_data = [n \in Nodes |-> {}]
    /\ client_acks = {}
    /\ epoch = 1

IsPrimary(node) == node = primary /\ alive[node]

ClientWrite(data) ==
    /\ IsPrimary(primary)
    /\ data \notin node_data[primary]
    /\ node_data' = [node_data EXCEPT ![primary] = @ \cup {data}]
    /\ client_acks' = client_acks \cup {data}
    /\ UNCHANGED <<primary, alive, epoch>>

ReplicateToNode(data, node) ==
    /\ alive[node]
    /\ node # primary
    /\ alive[primary]
    /\ data \in node_data[primary]
    /\ data \notin node_data[node]
    /\ node_data' = [node_data EXCEPT ![node] = @ \cup {data}]
    /\ UNCHANGED <<primary, alive, client_acks, epoch>>

NodeFailure(node) ==
    /\ alive[node]
    /\ alive' = [alive EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<primary, node_data, client_acks, epoch>>

NodeRecover(node) ==
    /\ ~alive[node]
    /\ alive' = [alive EXCEPT ![node] = TRUE]
    /\ UNCHANGED <<primary, node_data, client_acks, epoch>>

PromoteReplica(new_primary) ==
    /\ ~alive[primary]
    /\ alive[new_primary]
    /\ new_primary # primary
    /\ primary' = new_primary
    /\ node_data' = [node_data EXCEPT ![new_primary] = node_data[new_primary]]
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<alive, client_acks>>

Next ==
    \/ \E data \in 1..MaxWrites : ClientWrite(data)
    \/ \E data \in 1..MaxWrites, n \in Nodes : ReplicateToNode(data, n)
    \/ \E n \in Nodes : NodeFailure(n)
    \/ \E n \in Nodes : NodeRecover(n)
    \/ \E n \in Nodes : PromoteReplica(n)

LiveNodeCount(d) ==
    Cardinality({n \in Nodes : alive[n] /\ d \in node_data[n]})

AnyNodeAlive ==
    Cardinality({n \in Nodes : alive[n]}) >= 1

InvAckedDataDurable ==
    \A d \in 1..MaxWrites : (d \in client_acks /\ AnyNodeAlive) => (LiveNodeCount(d) >= 1)

InvEpochPositive ==
    epoch >= 1

====
