---- MODULE tail_of_empty_string ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvTail == Tail("") = ""
====
