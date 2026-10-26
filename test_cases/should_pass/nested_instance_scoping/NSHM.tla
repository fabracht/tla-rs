---- MODULE NSHM ----
EXTENDS Naturals
VARIABLE y
RECURSIVE H(_)
H(n) == IF n = 0 THEN 10 ELSE 1 + H(n - 1)
J == INSTANCE NSHL WITH z <- H(y)
ReadH == J!Val
====
