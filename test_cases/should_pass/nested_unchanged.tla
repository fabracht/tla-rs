---- MODULE nested_unchanged ----
EXTENDS Naturals, Sequences
VARIABLES x, y, l
vars == <<x, y>>
tvars == <<vars, l>>
Trace == <<1, 2, 3>>
alias == y
deep == <<<<x>>, <<alias, l>>>>
Init == x = 0 /\ y = 0 /\ l = 1
Step == l <= Len(Trace) /\ x' = Trace[l] /\ l' = l + 1 /\ UNCHANGED y
Done == l > Len(Trace) /\ UNCHANGED <<vars, l>>
Idle == l > Len(Trace) /\ UNCHANGED deep
Next == Step \/ Done \/ Idle
Spec == Init /\ [][Next]_tvars /\ WF_tvars(Step)
Finished == <>(l > Len(Trace))
====
