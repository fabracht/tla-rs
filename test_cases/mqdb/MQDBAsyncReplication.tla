---- MODULE MQDBAsyncReplication ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWrites

VARIABLES
    primary,
    alive,
    node_data,
    ack_counts,
    client_acks,
    epoch

vars == <<primary, alive, node_data, ack_counts, client_acks, epoch>>

Quorum == (Cardinality(Nodes) / 2) + 1

Init ==
    /\ primary \in Nodes
    /\ alive = [n \in Nodes |-> TRUE]
    /\ node_data = [n \in Nodes |-> {}]
    /\ ack_counts = [d \in 1..MaxWrites |-> 0]
    /\ client_acks = {}
    /\ epoch = 1

IsPrimary(node) == node = primary /\ alive[node]

ClientWrite(data) ==
    /\ IsPrimary(primary)
    /\ data \notin node_data[primary]
    /\ node_data' = [node_data EXCEPT ![primary] = @ \cup {data}]
    /\ ack_counts' = [ack_counts EXCEPT ![data] = 1]
    /\ UNCHANGED <<primary, alive, client_acks, epoch>>

ReplicateToNode(data, node) ==
    /\ alive[node]
    /\ node # primary
    /\ alive[primary]
    /\ data \in node_data[primary]
    /\ data \notin node_data[node]
    /\ ack_counts[data] >= 1
    /\ node_data' = [node_data EXCEPT ![node] = @ \cup {data}]
    /\ ack_counts' = [ack_counts EXCEPT ![data] = @ + 1]
    /\ UNCHANGED <<primary, alive, client_acks, epoch>>

QuorumAck(data) ==
    /\ ack_counts[data] >= Quorum
    /\ data \notin client_acks
    /\ alive[primary]
    /\ client_acks' = client_acks \cup {data}
    /\ UNCHANGED <<primary, alive, node_data, ack_counts, epoch>>

NodeFailure(node) ==
    /\ alive[node]
    /\ alive' = [alive EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<primary, node_data, ack_counts, client_acks, epoch>>

NodeRecover(node) ==
    /\ ~alive[node]
    /\ alive' = [alive EXCEPT ![node] = TRUE]
    /\ UNCHANGED <<primary, node_data, ack_counts, client_acks, epoch>>

PromoteReplica(new_primary) ==
    /\ ~alive[primary]
    /\ alive[new_primary]
    /\ new_primary # primary
    /\ primary' = new_primary
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<alive, node_data, ack_counts, client_acks>>

Next ==
    \/ \E data \in 1..MaxWrites : ClientWrite(data)
    \/ \E data \in 1..MaxWrites, n \in Nodes : ReplicateToNode(data, n)
    \/ \E data \in 1..MaxWrites : QuorumAck(data)
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
