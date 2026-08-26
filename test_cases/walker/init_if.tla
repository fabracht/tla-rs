---- MODULE init_if ----
EXTENDS Naturals
VARIABLES x
Init == IF TRUE THEN x = 2 ELSE x = 1
Next == UNCHANGED x
Inv == x # 2
====
