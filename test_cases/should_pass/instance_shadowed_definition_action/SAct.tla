---- MODULE SAct ----
EXTENDS Naturals
VARIABLE y
C == 9
INSTANCE SLeafA
MNext == y < 9 /\ y' = Val
Reached == y = Val
====
