---- MODULE set_membership ----
EXTENDS SMBase
Bounded(S) == UNION {[1..n -> S] : n \in 0..3}
Below(k) == {n \in 1..N : n < k}
a \oplus b == {a, b, x}
Init == x = 0
Next == x < 2 /\ x' = x + 1
Evens == {n \in 0..10 : n % 2 = 0}
Constant == /\ x \in Evens <=> x % 2 = 0
            /\ 12 \notin Evens
            /\ 3 \in UNION {{1, 2}, {3}}
            /\ (CHOOSE n \in Evens : n > 7) = 8
            /\ [[i \in 1..3 |-> i] EXCEPT ![2] = @ + 10][2] = 12
Overridden == /\ <<1, 2, 2>> \in Sorted
              /\ <<2, 1>> \notin Sorted
              /\ <<1, 1, 1, 1>> \notin Sorted
StateDependent == /\ Cardinality({n \in 0..3 : n > x}) = 3 - x
                  /\ Cardinality(Above) = N - x
BoundDependent == \A k \in 1..N : /\ Cardinality({n \in 1..N : n <= k}) = k
                                  /\ Cardinality(Below(k)) = k - 1
                                  /\ <<k, k>> \in Bounded({k})
                                  /\ <<k + 1>> \notin Bounded({k})
InfixDependent == Cardinality(1 \oplus 2) = IF x \in {1, 2} THEN 2 ELSE 3
LetDependent == LET S == {x, x + 1} IN Cardinality({n \in S : n > 0}) = IF x = 0 THEN 1 ELSE 2
====
