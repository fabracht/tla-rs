---- MODULE instance_with_caller_definition ----
EXTENDS Naturals, WBase, WUn
VARIABLE y
RECURSIVE Val(_)
Val(a) == IF a = 0 THEN 1 ELSE Val(a - 1)
g[i \in 1..2] == i
a \oplus b == a * b * 10
I == INSTANCE WM WITH c <- Foo
J == INSTANCE WM WITH c <- Bar
K == INSTANCE WM WITH c <- Val(1)
L == INSTANCE WM WITH c <- g[1]
P(k) == INSTANCE WM WITH c <- Foo + k
Init == y = 0
Next == y = 0 /\ I!Set(Foo)
InvGet == I!Get = 1 /\ J!Get = 1 /\ K!Get = 1 /\ L!Get = 1 /\ P(0)!Get = 1
InvSet == y \in {0, 1}
InvOwn == L!g[1] = 2 /\ L!Sum = 2
====
