---- MODULE InitBox ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = (x + 1) % 3 /\ y' = y
Spec == Init /\ [][Next]_<<x, y>>
Differ == [](x # y)
====
