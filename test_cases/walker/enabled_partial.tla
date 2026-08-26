---- MODULE enabled_partial ----
VARIABLES x, y
Act == x' = 1
Init == x = 0 /\ y = 0
Next == (x' = 1 /\ y' = y) \/ (UNCHANGED <<x,y>>)
Inv == ~(ENABLED Act)
====
