---- MODULE inline_channels ----
EXTENDS Naturals, Sequences

VARIABLE channels

Init ==
    channels = [i \in {"a", "b"} |-> <<>>]

Send(id, msg) ==
    /\ Len(channels[id]) < 2
    /\ channels' = [channels EXCEPT ![id] = Append(@, msg)]

Recv(id) ==
    /\ Len(channels[id]) > 0
    /\ channels' = [channels EXCEPT ![id] = Tail(@)]

Next ==
    \E id \in {"a", "b"}:
        \/ Send(id, "hello")
        \/ Recv(id)

TypeOK == TRUE

====
