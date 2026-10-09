---- MODULE sequence_concat_with_string ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvConcat == <<"a">> \o "b" = <<"a", "b">>
====
