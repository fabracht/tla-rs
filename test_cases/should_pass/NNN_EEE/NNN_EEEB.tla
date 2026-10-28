---- MODULE NNN_EEEB ----
EXTENDS Naturals, NNN_EEEBBase
Help2(n) == n + 10
J == INSTANCE NNN_EEELeaf WITH z <- Help2(y)
Read2 == J!Val3
====
