EXTENDS Naturals

VARIABLES x

Init == x \in 0..5

Next == x' \in Nat /\ x' = x + 1 /\ x < 10

Inv == x <= 10
