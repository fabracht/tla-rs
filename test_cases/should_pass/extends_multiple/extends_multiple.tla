---- MODULE extends_multiple ----
EXTENDS Naturals, MathOps, BoolOps

VARIABLES x

Init == x = 1
Next == x' = IF x < 4 THEN Double(x) ELSE x
Inv == x \in 1..8 /\ (x > 1 => IsEven(x))
====
