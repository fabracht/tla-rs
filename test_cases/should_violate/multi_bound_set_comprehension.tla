---- MODULE multi_bound_set_comprehension ----
EXTENDS Integers
VARIABLE x
S == { a * 10 + b : a \in {1, 2}, b \in {3, 4} }
Init == x \in S
Next == UNCHANGED x
Inv == x # 24
====
