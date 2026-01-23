---- MODULE boolean_set ----

VARIABLES x

Init == x \in BOOLEAN

Next == x' = ~x

Inv == x \in BOOLEAN

====
