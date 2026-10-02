---- MODULE Enabled2 ----
EXTENDS Naturals
CONSTANT P
VARIABLES pc, lock, y
vars == <<pc, lock, y>>
Init == pc = [p \in P |-> "idle"] /\ lock = "none" /\ y = 0
Try(p) == pc[p] = "idle" /\ pc' = [pc EXCEPT ![p] = "wait"] /\ UNCHANGED <<lock, y>>
Enter(p) == pc[p] = "wait" /\ lock = "none" /\ pc' = [pc EXCEPT ![p] = "cs"] /\ lock' = p /\ UNCHANGED y
Exit(p) == pc[p] = "cs" /\ pc' = [pc EXCEPT ![p] = "idle"] /\ lock' = "none" /\ UNCHANGED y
Bump == y < 1 /\ y' = y + 1 /\ UNCHANGED <<pc, lock>>
Next == (\E p \in P : Try(p) \/ Enter(p) \/ Exit(p)) \/ Bump
SpecWF == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
SpecAssume == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Exit(p)) /\ []<>~ENABLED Enter(p)
CanEnter(p) == ENABLED Enter(p)
ParamEnabled == \A p \in P : [](CanEnter(p) => <>(pc[p] = "cs"))
LetEnabled == LET can(p) == ENABLED Enter(p) IN \A p \in P : []<>~can(p)
SomeEnter == []<>~ENABLED (\E p \in P : Enter(p))
SomeEnterWF == WF_vars(\E p \in P : Enter(p))
PartialEnabled == []<>ENABLED (y' = 1)
PartialWF == WF_y(y' = y + 1)
BumpWF == WF_y(Bump)
BumpEventually == <>(y = 1)
SFAnyEnter == SF_vars(\E p \in P : Enter(p))
QuantWFSome == \E p \in P : WF_vars(Enter(p))
EnterOrExitSF == \A p \in P : SF_vars(Enter(p) \/ Exit(p))
====
