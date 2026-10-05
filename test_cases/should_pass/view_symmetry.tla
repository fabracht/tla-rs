---- MODULE view_symmetry ----
EXTENDS Naturals, Sequences, TLC
CONSTANT P
VARIABLES log, seen
Init == log = <<>> /\ seen = "none"
Add(p) == Len(log) < 2 /\ log' = Append(log, p) /\ UNCHANGED seen
See(p) == seen = "none" /\ Len(log) = 2 /\ seen' = p /\ UNCHANGED log
Next == \E p \in P : Add(p) \/ See(p)
View == <<Len(log), seen>>
Perms == Permutations(P)
====
