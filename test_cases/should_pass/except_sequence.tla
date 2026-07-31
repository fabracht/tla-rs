---- MODULE except_sequence ----

EXTENDS Naturals, Sequences

VARIABLE x

Init == x = 0
Next == x' = 1 - x

tup == <<10, 20, 30>>
nested == <<[a |-> 1], <<5, 6>>>>
recseq == [s |-> <<1, 2>>]

InvT1 == [tup EXCEPT ![1] = 9] = <<9, 20, 30>>
InvT2 == [tup EXCEPT ![3] = 9] = <<10, 20, 9>>
InvT3 == [tup EXCEPT ![2] = @ + 5] = <<10, 25, 30>>
InvT4 == [tup EXCEPT ![1] = 9, ![3] = 7] = <<9, 20, 7>>
InvN1 == [nested EXCEPT ![1].a = 4] = <<[a |-> 4], <<5, 6>>>>
InvN2 == [nested EXCEPT ![2][1] = 8] = <<[a |-> 1], <<8, 6>>>>
InvR1 == [recseq EXCEPT !.s[2] = 9] = [s |-> <<1, 9>>]

====
