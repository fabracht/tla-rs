---- MODULE SMBase ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT N
VARIABLE x
Sorted == {s \in Seq(1..N) : \A i \in 1..Len(s) - 1 : s[i] <= s[i + 1]}
Above == {n \in 0..N : n > x}
====
