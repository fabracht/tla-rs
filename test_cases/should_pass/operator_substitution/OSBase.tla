---- MODULE OSBase ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Limit
VARIABLES x, s
Init == x = 0 /\ s = <<>>
Bump(n) == n + 1
Next == x < Limit /\ x' = Bump(x) /\ s' \in Seq({x})
InvNat == Cardinality(Nat) = 4
Spec == Init /\ [][Next]_<<x, s>>
====
