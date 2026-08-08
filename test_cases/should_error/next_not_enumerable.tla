---- MODULE next_not_enumerable ----

EXTENDS Naturals, Sequences

VARIABLE x

Init == x = <<>>

Next == x' \in Seq({1, 2}) /\ Len(x') = 1

Inv == Len(x) = 0

====
