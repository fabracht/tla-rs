---- MODULE capture_disjunct ----
EXTENDS Naturals
VARIABLES x, y, z
Pick(a) == \E i \in {5, 6} : a = i
Init == x = 0 /\ y = 0 /\ z = 0
Step == \E i \in {1, 2} :
          /\ x' = i
          /\ Pick(y')
          /\ (z' = i \/ z' = i + 10)
Next == Step \/ UNCHANGED <<x, y, z>>
Inv == (x # 0) => (z = x \/ z = x + 10)
====
