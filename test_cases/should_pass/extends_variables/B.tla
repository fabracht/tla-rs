---- MODULE B ----
EXTENDS D
VARIABLE b
BStep == b' = 1 - b /\ UNCHANGED d
====
