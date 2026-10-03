---- MODULE SymMutex ----
EXTENDS Naturals, TLC
CONSTANT P
VARIABLES pc, lock
vars == <<pc, lock>>
Init == pc = [p \in P |-> "idle"] /\ lock = "none"
Try(p) == pc[p] = "idle" /\ pc' = [pc EXCEPT ![p] = "wait"] /\ UNCHANGED lock
Enter(p) == pc[p] = "wait" /\ lock = "none" /\ pc' = [pc EXCEPT ![p] = "cs"] /\ lock' = p
Exit(p) == pc[p] = "cs" /\ pc' = [pc EXCEPT ![p] = "idle"] /\ lock' = "none"
Next == \E p \in P : Try(p) \/ Enter(p) \/ Exit(p)
Sym == Permutations(P)
SpecWF == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
SpecSF == Init /\ [][Next]_vars /\ \A p \in P : SF_vars(Enter(p)) /\ WF_vars(Exit(p))
SpecAll == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Try(p) \/ Enter(p) \/ Exit(p))
SpecNext == Init /\ [][Next]_vars /\ WF_vars(Next)
SpecNone == Init /\ [][Next]_vars
Progress == (\E p \in P : pc[p] = "wait") ~> (\E p \in P : pc[p] = "cs")
StarveFree == \A p \in P : pc[p] = "wait" ~> pc[p] = "cs"
SomeIdle == []<>(\E p \in P : pc[p] = "idle")
LockFree == []<>(lock = "none")
EnterSF == \A p \in P : SF_vars(Enter(p))
ExitWF == \A p \in P : WF_vars(Exit(p))
SomeCS == []<>(\E p \in P : pc[p] = "cs")
EnterOften == []<><<\E p \in P : Enter(p)>>_vars
EventuallyAllIdle == <>[](\A p \in P : pc[p] = "idle")
====
