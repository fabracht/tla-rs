---- MODULE NNMid ----
EXTENDS Naturals
CONSTANT C
VARIABLE y
J == INSTANCE NNLeaf WITH z <- y + 1
K == INSTANCE NNLeaf WITH z <- y
Read == J!Val
ReadC == K!Const
====
