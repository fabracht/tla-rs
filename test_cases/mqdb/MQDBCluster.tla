---- MODULE MQDBCluster ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Partitions, MaxSeq

VARIABLES primary, epoch, seq, committed, alive

vars == <<primary, epoch, seq, committed, alive>>

Quorum == (Cardinality(Nodes) / 2) + 1

Init ==
    /\ primary \in [Partitions -> Nodes]
    /\ epoch = [p \in Partitions |-> 1]
    /\ seq = [n \in Nodes |-> [p \in Partitions |-> 0]]
    /\ committed = [p \in Partitions |-> 0]
    /\ alive = [n \in Nodes |-> TRUE]

IsPrimary(node, part) ==
    primary[part] = node /\ alive[node]

ClientWrite(node, part) ==
    /\ IsPrimary(node, part)
    /\ seq[node][part] < MaxSeq
    /\ seq' = [seq EXCEPT ![node] = [@ EXCEPT ![part] = @ + 1]]
    /\ UNCHANGED <<primary, epoch, committed, alive>>

ReplicateWrite(pr, rp, part) ==
    /\ IsPrimary(pr, part)
    /\ alive[rp]
    /\ rp # pr
    /\ seq[rp][part] < seq[pr][part]
    /\ seq' = [seq EXCEPT ![rp] = [@ EXCEPT ![part] = @ + 1]]
    /\ UNCHANGED <<primary, epoch, committed, alive>>

QuorumCommit(part) ==
    /\ LET pr == primary[part]
       IN /\ alive[pr]
          /\ committed[part] < seq[pr][part]
    /\ LET next_commit == committed[part] + 1
           acked == {n \in Nodes : alive[n] /\ seq[n][part] >= next_commit}
       IN /\ Cardinality(acked) >= Quorum
          /\ committed' = [committed EXCEPT ![part] = next_commit]
    /\ UNCHANGED <<primary, epoch, seq, alive>>

NodeFailure(node) ==
    /\ alive[node]
    /\ alive' = [alive EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<primary, epoch, seq, committed>>

NodeRecover(node) ==
    /\ ~alive[node]
    /\ alive' = [alive EXCEPT ![node] = TRUE]
    /\ UNCHANGED <<primary, epoch, seq, committed>>

PromoteReplica(part, new_primary) ==
    /\ ~alive[primary[part]]
    /\ alive[new_primary]
    /\ new_primary # primary[part]
    /\ primary' = [primary EXCEPT ![part] = new_primary]
    /\ epoch' = [epoch EXCEPT ![part] = @ + 1]
    /\ UNCHANGED <<seq, committed, alive>>

Next ==
    \/ \E n \in Nodes, p \in Partitions : ClientWrite(n, p)
    \/ \E pr \in Nodes, rp \in Nodes, p \in Partitions : ReplicateWrite(pr, rp, p)
    \/ \E p \in Partitions : QuorumCommit(p)
    \/ \E n \in Nodes : NodeFailure(n)
    \/ \E n \in Nodes : NodeRecover(n)
    \/ \E p \in Partitions, n \in Nodes : PromoteReplica(p, n)

InvSinglePrimary ==
    \A p \in Partitions : primary[p] \in Nodes

InvEpochMonotonic ==
    \A p \in Partitions : epoch[p] >= 1

InvCommittedBounded ==
    \A p \in Partitions : committed[p] <= MaxSeq

====
