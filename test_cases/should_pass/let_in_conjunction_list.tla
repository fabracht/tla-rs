---- MODULE let_in_conjunction_list ----
EXTENDS Integers
VARIABLES x, y
Init == /\ x = LET f == 6 IN f
        /\ y = 0
Next == UNCHANGED <<x, y>>
Inv == x = 6 /\ y = 0
====
