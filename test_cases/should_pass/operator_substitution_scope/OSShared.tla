---- MODULE OSShared ----
EXTENDS Naturals, Sequences
Val == 7
UsesVal == Val + 1
LongOnes(S) == IF \E s \in S : Len(s) > 1 THEN 0 ELSE 1
SeqSmall == LongOnes(Seq({1}))
====
