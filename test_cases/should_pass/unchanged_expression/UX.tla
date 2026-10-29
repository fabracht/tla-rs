---- MODULE UX ----
EXTENDS Naturals
VARIABLES y, z
Bump == z < 2 /\ z' = z + 1 /\ UNCHANGED y
====
