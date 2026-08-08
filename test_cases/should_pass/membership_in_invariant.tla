---- MODULE membership_in_invariant ----

EXTENDS Naturals, Sequences

VARIABLE q

Init == q = { <<1>>, <<>> }

Next == UNCHANGED q

InvNested == q \in SUBSET Seq({1, 2})

InvPowerset == {{1}, {2}} \in SUBSET SUBSET {1, 2}

InvRecordSet == [a |-> <<1>>] \in [a: Seq({1, 2})]

InvFnSet == [i \in 1 .. 2 |-> <<i>>] \in [1 .. 2 -> Seq({1, 2})]

====
