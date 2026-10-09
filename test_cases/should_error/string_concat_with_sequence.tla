---- MODULE string_concat_with_sequence ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == UNCHANGED x
InvConcat == "ab" \o <<"c">> = "abc"
====
