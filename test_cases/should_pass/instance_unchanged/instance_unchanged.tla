---- MODULE instance_unchanged ----
EXTENDS Naturals
VARIABLES p, q, r
vars == <<p, q, r>>
I == INSTANCE UNM WITH y <- p, z <- q, w <- r
Init == p = 0 /\ q = 0 /\ r = 0
Next == I!Bump
Inv == p = 0 /\ r = 0 /\ q \in 0..2
====
