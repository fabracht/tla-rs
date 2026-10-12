---- MODULE prime_parameters ----
EXTENDS Naturals, Sequences
CONSTANT K
VARIABLES w, log, x, y, z, u, v
vars == <<w, log, x, y, z, u, v>>
P == INSTANCE PNext
Init == w = [i \in 1..2 |-> 0] /\ log = <<>> /\ x = 0 /\ y = 0 /\ z = K /\ u = K /\ v = 0
After(a) == a'
Twice(a) == After(a) * 2
a \oplus b == a' + b
Bump(p) == /\ w' = [w EXCEPT ![p] = @ + 1]
           /\ log' = log \o <<w[p]'>>
Next == /\ x < 2
        /\ x' = x + 1
        /\ \E p \in 1..2 : w[p] < 1 /\ Bump(p)
        /\ y' = Twice(x)
        /\ z' = LET n == x IN n' + K'
        /\ u' = x \oplus K
        /\ v' = P!Later(x)
InvLog == \A i \in DOMAIN log : log[i] = 1
InvTwice == y = 2 * x
InvLet == z = x + K
InvInfix == u = x + K
InvInstance == v = x
====
