---- MODULE NNUnnamed ----
EXTENDS Naturals
CONSTANT D
VARIABLE u
L == INSTANCE NNLeaf WITH z <- u, C <- D
Twice == L!Val + L!Val
====
