---- MODULE undefined_in_seq_domain ----

EXTENDS Naturals, Sequences

VARIABLE q

Msgs == {1, 2, 3}

Init == q = <<>>

Next == UNCHANGED q

TypeOK == q \in Seq(Msg)

====
