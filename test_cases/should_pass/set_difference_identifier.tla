---- MODULE set_difference_identifier ----
EXTENDS Integers
VARIABLE x
Versions == 0..4
Pick(used) == CHOOSE v \in Versions\used : v >= 0
Init == x = Pick({0})
Next == x' = x
InvPick == x = 1
InvIntersect == ({1, 2} \intersect {2, 3}) = {2}
InvUnion == (Versions\union{9}) = Versions \cup {9}
====
