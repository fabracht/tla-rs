---- MODULE NNU_EEE_defB ----
EXTENDS Naturals, NNU_EEE_defBBase
C3 == 9
Help2(n) == n + 10
INSTANCE NNU_EEE_defLeaf WITH z <- Help2(y)
Read2 == Val3
====
