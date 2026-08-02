---- MODULE init_not_enumerable ----

EXTENDS Naturals, Sequences

VARIABLE x

Init == x \in Seq({1, 2}) /\ Len(x) = 1

Next == UNCHANGED x

Inv == Len(x) = 0

====
