---- MODULE OSOwn ----
EXTENDS Naturals
VARIABLE x
Init == x = 7
HasLim == \E Lim \in {3} : Lim = 3
====
