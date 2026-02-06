---- MODULE parameterized_instance ----
EXTENDS Naturals, Sequences

CONSTANT Ids

VARIABLE channels

Channel(id) == INSTANCE SimpleChannel WITH buffer <- channels[id]

Init ==
    channels = [i \in Ids |-> <<>>]

Send(id, msg) ==
    /\ Len(channels[id]) < 2
    /\ Channel(id)!Send(msg)

Recv(id) ==
    Channel(id)!Recv

Next ==
    \E id \in Ids:
        \/ Send(id, "hello")
        \/ Recv(id)

TypeOK ==
    \A id \in Ids: Channel(id)!TypeOK

====
