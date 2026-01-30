---- MODULE sync_leads_to ----
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Diagrams, MaxDeliveries

VARIABLES
    subscriptions,
    pending_diagram,
    delivered_count

vars == <<subscriptions, pending_diagram, delivered_count>>

Init ==
    /\ subscriptions = [c \in Clients |-> {}]
    /\ pending_diagram = [c \in Clients |-> {}]
    /\ delivered_count = 0

Subscribe(c, d) ==
    /\ d \notin subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED <<pending_diagram, delivered_count>>

Unsubscribe(c, d) ==
    /\ d \in subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \ {d}]
    /\ pending_diagram' = [pending_diagram EXCEPT ![c] = @ \ {d}]
    /\ UNCHANGED delivered_count

Mutate(author, d) ==
    /\ d \in subscriptions[author]
    /\ LET recipients == {c \in Clients : d \in subscriptions[c] /\ c /= author}
       IN pending_diagram' = [c \in Clients |->
                        IF c \in recipients
                        THEN pending_diagram[c] \cup {d}
                        ELSE pending_diagram[c]]
    /\ UNCHANGED <<subscriptions, delivered_count>>

Deliver(c, d) ==
    /\ d \in pending_diagram[c]
    /\ delivered_count < MaxDeliveries
    /\ pending_diagram' = [pending_diagram EXCEPT ![c] = @ \ {d}]
    /\ delivered_count' = delivered_count + 1
    /\ UNCHANGED subscriptions

Next ==
    \/ \E c \in Clients, d \in Diagrams: Subscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Unsubscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Mutate(c, d)
    \/ \E c \in Clients, d \in Diagrams: Deliver(c, d)

\* Safety
InvNoPendingForUnsubscribed ==
    \A c \in Clients: \A d \in pending_diagram[c]: d \in subscriptions[c]

\* "Something is pending" predicate
SomethingPending == \E c \in Clients: pending_diagram[c] /= {}

\* "Something was delivered" predicate
SomethingDelivered == delivered_count > 0

\* Liveness: if something is pending, eventually something is delivered
\* WITHOUT fairness this should FAIL
Spec == Init /\ [][Next]_vars /\ (SomethingPending ~> SomethingDelivered)

====
