---- MODULE MutexFair ----
EXTENDS Naturals
CONSTANT P
VARIABLES pc, lock
vars == <<pc, lock>>
Init == pc = [p \in P |-> "idle"] /\ lock = "none"
Try(p) == pc[p] = "idle" /\ pc' = [pc EXCEPT ![p] = "wait"] /\ UNCHANGED lock
Enter(p) == pc[p] = "wait" /\ lock = "none" /\ pc' = [pc EXCEPT ![p] = "cs"] /\ lock' = p
Exit(p) == pc[p] = "cs" /\ pc' = [pc EXCEPT ![p] = "idle"] /\ lock' = "none"
Next == \E p \in P : Try(p) \/ Enter(p) \/ Exit(p)
SpecWF == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
SpecSF == Init /\ [][Next]_vars /\ \A p \in P : SF_vars(Enter(p)) /\ WF_vars(Exit(p))
ExitWF == \A p \in P : WF_vars(Exit(p))
EnterSF == \A p \in P : SF_vars(Enter(p))
EnterWF == \A p \in P : WF_vars(Enter(p))
SomeEnterSF == \E p \in P : SF_vars(Enter(p))
WaitEnabled == \A p \in P : [](pc[p] = "wait" /\ lock = "none" => ENABLED Enter(p))
EnterDisabledOften == \A p \in P : []<>~ENABLED Enter(p)
AbstractFair == Init /\ [][Next]_vars /\ \A p \in P : SF_vars(Enter(p))
====
