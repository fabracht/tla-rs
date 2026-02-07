------------------------------ MODULE MChannel ------------------------------

LOCAL INSTANCE TLC

CONSTANT Id
CONSTANT Data

VARIABLE channels

Null == <<>>

Channel == [val: Data \cup {Null}, busy: BOOLEAN]

TypeOK == channels[Id] \in Channel

Send(data) ==
   /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>)
   /\ \lnot channels[Id].busy
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val = data, !.busy = TRUE]]

Recv(data) ==
   /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>)
   /\ channels[Id].busy
   /\ data = channels[Id].val
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val=Null, !.busy = FALSE]]

Sending ==
   IF channels[Id].busy
   THEN {channels[Id].val}
   ELSE {}

InitValue == [val |-> Null, busy |-> FALSE]

=============================================================================
