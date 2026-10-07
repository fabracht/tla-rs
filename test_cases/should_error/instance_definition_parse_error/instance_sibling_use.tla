---- MODULE instance_sibling_use ----
VARIABLE x
H == INSTANCE Helpers
Init == x = H!UsesBad
Next == UNCHANGED x
====
