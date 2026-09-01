---- MODULE let_operator_in_assignment_rhs ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Update == x' = LET add10(a) == a + 10 IN add10(10)
InvTest == x # 20
Next == Update
====
