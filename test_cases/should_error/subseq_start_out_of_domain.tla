---- MODULE subseq_start_out_of_domain ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvSubSeq == SubSeq("abc", 0, 2) = "ab"
====
