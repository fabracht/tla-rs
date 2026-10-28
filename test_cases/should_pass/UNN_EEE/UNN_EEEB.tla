---- MODULE UNN_EEEB ----
EXTENDS Naturals, UNN_EEEBBase
Help2(n) == n + 10
J == INSTANCE UNN_EEELeaf WITH z <- Help2(y)
Read2 == J!Val3
====
