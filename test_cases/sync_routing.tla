---- MODULE sync_routing ----
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Diagrams, MaxMutations

VARIABLES
    subscriptions,  \* subscriptions[c] = set of diagrams client c is subscribed to
    pending,        \* pending[c] = set of {diagram, mutation_id} client c should receive
    delivered,      \* delivered[c] = set of {diagram, mutation_id} client c has received
    mutation_counter

vars == <<subscriptions, pending, delivered, mutation_counter>>

TypeOK ==
    /\ subscriptions \in [Clients -> SUBSET Diagrams]
    /\ mutation_counter \in 0..MaxMutations

Init ==
    /\ subscriptions = [c \in Clients |-> {}]
    /\ pending = [c \in Clients |-> {}]
    /\ delivered = [c \in Clients |-> {}]
    /\ mutation_counter = 0

Subscribe(c, d) ==
    /\ d \notin subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED <<pending, delivered, mutation_counter>>

Unsubscribe(c, d) ==
    /\ d \in subscriptions[c]
    /\ subscriptions' = [subscriptions EXCEPT ![c] = @ \ {d}]
    /\ UNCHANGED <<pending, delivered, mutation_counter>>

Mutate(author, d) ==
    /\ d \in subscriptions[author]
    /\ mutation_counter < MaxMutations
    /\ mutation_counter' = mutation_counter + 1
    /\ LET mut == <<d, mutation_counter'>>
           recipients == {c \in Clients : d \in subscriptions[c] /\ c /= author}
       IN pending' = [c \in Clients |->
                        IF c \in recipients
                        THEN pending[c] \cup {mut}
                        ELSE pending[c]]
    /\ UNCHANGED <<subscriptions, delivered>>

Deliver(c) ==
    /\ pending[c] /= {}
    /\ \E mut \in pending[c]:
        /\ pending' = [pending EXCEPT ![c] = @ \ {mut}]
        /\ delivered' = [delivered EXCEPT ![c] = @ \cup {mut}]
    /\ UNCHANGED <<subscriptions, mutation_counter>>

Next ==
    \/ \E c \in Clients, d \in Diagrams: Subscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Unsubscribe(c, d)
    \/ \E c \in Clients, d \in Diagrams: Mutate(c, d)
    \/ \E c \in Clients: Deliver(c)

\* Safety: Never deliver mutation to client not subscribed to that diagram
InvNoSpuriousDelivery ==
    \A c \in Clients: \A mut \in delivered[c]:
        LET d == mut[1] IN d \in subscriptions[c]

\* Safety: Never queue mutation for client not subscribed
InvNoPendingForUnsubscribed ==
    \A c \in Clients: \A mut \in pending[c]:
        LET d == mut[1] IN d \in subscriptions[c]

====
