---- MODULE Disj ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
StateOrLive == x = 1 \/ <>(x = 1)
BoxOrBox == [](x < 5) \/ [](x = 7)
NegAnd == ~((x = 0) /\ <>[](x = 0))
LiveOrLive == <>(x = 1) \/ <>(x = 7)
====
