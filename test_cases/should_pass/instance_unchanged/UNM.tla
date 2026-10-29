---- MODULE UNM ----
EXTENDS Naturals
VARIABLES y, z, w
vars == <<y>>
Bump == z < 2 /\ z' = z + 1 /\ UNCHANGED vars /\ UNCHANGED w
====
