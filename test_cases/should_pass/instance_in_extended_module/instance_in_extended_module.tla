---- MODULE instance_in_extended_module ----
EXTENDS Naturals, IMid
VARIABLE x
Init == x = 0
Next == x < 6 /\ x' = Grow(x)
InvEven == x % 2 = 0
====
