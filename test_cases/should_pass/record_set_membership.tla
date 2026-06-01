---- MODULE record_set_membership ----
EXTENDS Naturals, Sequences

MsgId == {10, 20}
PortId == {1, 2}

VARIABLE ports

PortRec == [ id : PortId, queue : Seq(MsgId) ]

Init == ports = { [id |-> 1, queue |-> << >>],
                  [id |-> 2, queue |-> << >>] }

Push(p, m) ==
    ports' = (ports \ {p}) \cup { [id |-> p.id, queue |-> Append(p.queue, m)] }

Next == \E p \in ports, m \in MsgId :
    /\ Len(p.queue) < 2
    /\ Push(p, m)

TypeOK == ports \subseteq PortRec

InvMembership ==
    /\ [id |-> 1, queue |-> << >>] \in PortRec
    /\ [id |-> 2, queue |-> <<10, 20>>] \in PortRec
    /\ [id |-> 9, queue |-> << >>] \notin PortRec
    /\ [id |-> 1, queue |-> <<99>>] \notin PortRec
    /\ [id |-> 1] \notin PortRec

====
