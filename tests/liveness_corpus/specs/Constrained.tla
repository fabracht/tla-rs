---- MODULE Constrained ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Init2 == x \in {0, 7}
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x
Spec2 == Init2 /\ [][Next]_x
Small == x < 2
Moderate == x < 5
ActBelow2 == [][x' < 2]_x
AlwaysBelow2 == [](x < 2)
AlwaysBelow3 == [](x < 3)
StartsAtZero == x = 0
====
