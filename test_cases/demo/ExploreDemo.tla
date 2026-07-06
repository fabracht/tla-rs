---- MODULE ExploreDemo ----
EXTENDS Integers
VARIABLES x, y

Init == x = 0 /\ y = 0

Fan == \E d \in {1, 2, 3} : x' = d /\ y' = y

Tick == y' = y + 1 /\ x' = x

Next == Fan \/ Tick
====
