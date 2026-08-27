---- MODULE let_in_conjunction_list_violation ----
EXTENDS Integers
VARIABLES x, y
Init == /\ x = LET f == 6 IN f
        /\ y = 0
Next == UNCHANGED <<x, y>>
Inv == y = 6
====
