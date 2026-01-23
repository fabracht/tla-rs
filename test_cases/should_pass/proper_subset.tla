VARIABLES x, y

Init == x = {1, 2} /\ y = {1, 2, 3}

Next == UNCHANGED <<x, y>>

Inv1 == x \subset y
Inv2 == ~(y \subset x)
Inv3 == x \subseteq y
