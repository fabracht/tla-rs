---- MODULE extends_variables ----
EXTENDS B, C
VARIABLE r
vars == <<d, b, c, r>>
RInit == d = 0 /\ b = 0 /\ c = {} /\ r = FALSE
RNext == \/ DStep /\ UNCHANGED <<b, c, r>>
         \/ BStep /\ UNCHANGED <<c, r>>
         \/ d = N /\ r' = TRUE /\ c' = c \cup {d} /\ UNCHANGED <<d, b>>
RSpec == RInit /\ [][RNext]_vars /\ WF_vars(DStep /\ UNCHANGED <<b, c, r>>) /\ WF_vars(d = N /\ r' = TRUE /\ c' = c \cup {d} /\ UNCHANGED <<d, b>>)
Done == <>(r = TRUE)
Typed == Cardinality(c) <= 1
====
