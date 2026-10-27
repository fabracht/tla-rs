---- MODULE instance_shadowed_definition ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
I == INSTANCE SMid
Init == x = 0
Next == x < 1 /\ x' = x + 1
InvGet == I!Read = 9
====
