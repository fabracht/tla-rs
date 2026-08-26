---- MODULE operator_arg_capture ----
VARIABLES sub, pd

Init ==
    /\ sub = [c \in {"c1", "c2"} |-> {"d1"}]
    /\ pd = [c \in {"c1", "c2"} |-> {}]

Mutate(author, d) ==
    /\ d \in sub[author]
    /\ LET recipients == {c \in {"c1", "c2"} : d \in sub[c] /\ c /= author}
       IN pd' = [c \in {"c1", "c2"} |->
                    IF c \in recipients THEN pd[c] \cup {d} ELSE pd[c]]
    /\ UNCHANGED sub

Next == \E c \in {"c1", "c2"}, d \in {"d1"} : Mutate(c, d)

Inv == \A c \in {"c1", "c2"} : pd[c] = {}
====
