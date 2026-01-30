---- MODULE sync_reconnect_clear ----
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Diagrams

VARIABLES
    subscriptions,
    pending,
    connected,
    delivered

vars == <<subscriptions, pending, connected, delivered>>

Init ==
    /\ subscriptions = [c \in Clients |-> {}]
    /\ pending = [c \in Clients |-> {}]
    /\ connected = [c \in Clients |-> TRUE]
    /\ delivered = [c \in Clients |-> {}]

Connect(c) ==
    /\ connected[c] = FALSE
    /\ connected' = [connected EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<subscriptions, pending, delivered>>

\* OPTION A: Clear both subscriptions and pending on disconnect
\* Client must re-subscribe and re-sync on reconnect
Disconnect(c) ==
    /\ connected[c] = TRUE
    /\ connected' = [connected EXCEPT ![c] = FALSE]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = {}]
    /\ pending' = [pending EXCEPT ![c] = {}]
    /\ UNCHANGED delivered

Subscribe(c, d) ==
    /\ connected[c] = TRUE
    /\ d \notin subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED <<pending, connected, delivered>>

Unsubscribe(c, d) ==
    /\ connected[c] = TRUE
    /\ d \in subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \ {d}]
    /\ pending' = [pending EXCEPT ![c] = @ \ {d}]
    /\ UNCHANGED <<connected, delivered>>

Mutate(author, d) ==
    /\ connected[author] = TRUE
    /\ d \in subscriptions[author]
    /\ LET recipients == {c \in Clients : d \in subscriptions[c] /\ c /= author}
       IN pending' = [c \in Clients |->
                        IF c \in recipients
                        THEN pending[c] \cup {d}
                        ELSE pending[c]]
    /\ UNCHANGED <<subscriptions, connected, delivered>>

Deliver(c, d) ==
    /\ connected[c] = TRUE
    /\ d \in pending[c]
    /\ pending' = [pending EXCEPT ![c] = @ \ {d}]
    /\ delivered' = [delivered EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED <<subscriptions, connected>>

Next ==
    \/ \E c \in Clients: Connect(c)
    \/ \E c \in Clients: Disconnect(c)
    \/ \E c \in Clients, d \in Diagrams: Subscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Unsubscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Mutate(c, d)
    \/ \E c \in Clients, d \in Diagrams: Deliver(c, d)

\* Safety: no pending for unsubscribed diagrams
InvNoPendingForUnsubscribed ==
    \A c \in Clients: \A d \in pending[c]: d \in subscriptions[c]

\* Safety: disconnected clients have no subscriptions or pending
InvDisconnectedClean ==
    \A c \in Clients: connected[c] = FALSE =>
        (subscriptions[c] = {} /\ pending[c] = {})

====
