---- MODULE enabled_holds ----
VARIABLES x, y
Guard == x' = 1
Init == x = 0 /\ y = 0
Next == (x' = 1 /\ y' = y) \/ UNCHANGED <<x,y>>
Inv == (x = 0) => ENABLED Guard
====
