---- MODULE subseq_end_out_of_domain ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvSubSeq == SubSeq(<<1, 2>>, 1, 3) = <<1, 2>>
====
