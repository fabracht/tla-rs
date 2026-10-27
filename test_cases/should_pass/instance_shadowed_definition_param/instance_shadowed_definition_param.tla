---- MODULE instance_shadowed_definition_param ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
P(k) == INSTANCE SMid WITH K <- k
Init == x = 0
Next == x < 1 /\ x' = x + 1
InvGet == P(1)!Read = 9
====
