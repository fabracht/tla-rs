---- MODULE MQDBCluster ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Partitions, MaxSeq

VARIABLES primary, epoch, seq, committed, alive, inflight_writes, write_epochs

vars == <<primary, epoch, seq, committed, alive, inflight_writes, write_epochs>>

Quorum == (Cardinality(Nodes) / 2) + 1

Init ==
    /\ primary \in [Partitions -> Nodes]
    /\ epoch = [p \in Partitions |-> 1]
    /\ seq = [n \in Nodes |-> [p \in Partitions |-> 0]]
    /\ committed = [p \in Partitions |-> 0]
    /\ alive = [n \in Nodes |-> TRUE]
    /\ inflight_writes = {}
    /\ write_epochs = [n \in Nodes |-> [p \in Partitions |-> 0]]

IsPrimary(node, part) ==
    primary[part] = node /\ alive[node]

StartWrite(node, part) ==
    /\ IsPrimary(node, part)
    /\ seq[node][part] < MaxSeq
    /\ inflight_writes' = inflight_writes \cup {<<node, part, epoch[part]>>}
    /\ UNCHANGED <<primary, epoch, seq, committed, alive, write_epochs>>

CompleteWrite(node, part, write_epoch) ==
    /\ <<node, part, write_epoch>> \in inflight_writes
    /\ seq' = [seq EXCEPT ![node] = [@ EXCEPT ![part] = @ + 1]]
    /\ write_epochs' = [write_epochs EXCEPT ![node] = [@ EXCEPT ![part] = write_epoch]]
    /\ inflight_writes' = inflight_writes \ {<<node, part, write_epoch>>}
    /\ UNCHANGED <<primary, epoch, committed, alive>>

ReplicateWrite(pr, rp, part) ==
    /\ IsPrimary(pr, part)
    /\ alive[rp]
    /\ rp # pr
    /\ seq[rp][part] < seq[pr][part]
    /\ seq' = [seq EXCEPT ![rp] = [@ EXCEPT ![part] = @ + 1]]
    /\ UNCHANGED <<primary, epoch, committed, alive, inflight_writes, write_epochs>>

QuorumCommit(part) ==
    /\ LET pr == primary[part]
       IN /\ alive[pr]
          /\ committed[part] < seq[pr][part]
    /\ LET next_commit == committed[part] + 1
           acked == {n \in Nodes : alive[n] /\ seq[n][part] >= next_commit}
       IN /\ Cardinality(acked) >= Quorum
          /\ committed' = [committed EXCEPT ![part] = next_commit]
    /\ UNCHANGED <<primary, epoch, seq, alive, inflight_writes, write_epochs>>

NodeFailure(node) ==
    /\ alive[node]
    /\ alive' = [alive EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<primary, epoch, seq, committed, inflight_writes, write_epochs>>

NodeRecover(node) ==
    /\ ~alive[node]
    /\ alive' = [alive EXCEPT ![node] = TRUE]
    /\ UNCHANGED <<primary, epoch, seq, committed, inflight_writes, write_epochs>>

PromoteReplica(part, new_primary) ==
    /\ ~alive[primary[part]]
    /\ alive[new_primary]
    /\ new_primary # primary[part]
    /\ primary' = [primary EXCEPT ![part] = new_primary]
    /\ epoch' = [epoch EXCEPT ![part] = @ + 1]
    /\ UNCHANGED <<seq, committed, alive, inflight_writes, write_epochs>>

Next ==
    \/ \E n \in Nodes, p \in Partitions : StartWrite(n, p)
    \/ \E n \in Nodes, p \in Partitions, e \in 1..5 :
        (<<n, p, e>> \in inflight_writes /\ CompleteWrite(n, p, e))
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

InvNoStaleEpochWrite ==
    \A n \in Nodes, p \in Partitions :
        (IsPrimary(n, p) /\ write_epochs[n][p] # 0) => write_epochs[n][p] = epoch[p]

====
