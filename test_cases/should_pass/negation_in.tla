---- MODULE negation_in ----
VARIABLE state

Init ==
  /\ state = "foo"
  /\ ~state \in { "bar", "baz" }

Next == state' = state

Inv == state = "foo"
====
