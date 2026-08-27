---- MODULE underscore_identifiers ----
EXTENDS Integers
VARIABLE x
Bump(__n) == __n + 1
Init == x = 0
Next == \E __p \in {1, 2} : x' = Bump(__p)
Inv == x < 10
====
