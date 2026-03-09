---- MODULE extends_transitive ----
EXTENDS MidLib

VARIABLES x, y

Init == x = 0 /\ y = 5
Next ==
    /\ x' = IF x < 3 THEN x + 1 ELSE x
    /\ y' = IF y > 2 THEN y - 1 ELSE y
Inv == Dist(x, y) <= 5
====
