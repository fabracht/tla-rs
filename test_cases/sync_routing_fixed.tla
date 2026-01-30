---- MODULE sync_routing_fixed ----
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Diagrams

VARIABLES
    subscriptions,
    pending_diagram

Init ==
    /\ subscriptions = [c \in Clients |-> {}]
    /\ pending_diagram = [c \in Clients |-> {}]

Subscribe(c, d) ==
    /\ d \notin subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED pending_diagram

Unsubscribe(c, d) ==
    /\ d \in subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \ {d}]
    /\ pending_diagram' = [pending_diagram EXCEPT ![c] = @ \ {d}]  \* FIX: clear pending

Mutate(author, d) ==
    /\ d \in subscriptions[author]
    /\ LET recipients == {c \in Clients : d \in subscriptions[c] /\ c /= author}
       IN pending_diagram' = [c \in Clients |->
                        IF c \in recipients
                        THEN pending_diagram[c] \cup {d}
                        ELSE pending_diagram[c]]
    /\ UNCHANGED subscriptions

Deliver(c, d) ==
    /\ d \in pending_diagram[c]
    /\ pending_diagram' = [pending_diagram EXCEPT ![c] = @ \ {d}]
    /\ UNCHANGED subscriptions

Next ==
    \/ \E c \in Clients, d \in Diagrams: Subscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Unsubscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Mutate(c, d)
    \/ \E c \in Clients, d \in Diagrams: Deliver(c, d)

InvNoPendingForUnsubscribed ==
    \A c \in Clients: \A d \in pending_diagram[c]: d \in subscriptions[c]

====
