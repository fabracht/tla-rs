---- MODULE operator_substitution_fairness ----
EXTENDS OSFairBase
MCSpec == Init /\ [][Next]_x /\ WF_x(Next)
====
