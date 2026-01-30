---- MODULE sync_initial_state_buggy ----
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Diagrams, MaxSeq

VARIABLES
    diagram_seq,
    subscribed,
    awaiting_state,
    buffered_seq,
    client_applied_seq,
    inflight_mutations

vars == <<diagram_seq, subscribed, awaiting_state, buffered_seq, client_applied_seq, inflight_mutations>>

SeqRange == 0..MaxSeq

Init ==
    /\ diagram_seq = [d \in Diagrams |-> 0]
    /\ subscribed = [c \in Clients |-> {}]
    /\ awaiting_state = [c \in Clients |-> {}]
    /\ buffered_seq = [c \in Clients |-> [d \in Diagrams |-> {}]]
    /\ client_applied_seq = [c \in Clients |-> [d \in Diagrams |-> -1]]
    /\ inflight_mutations = [c \in Clients |-> {}]

Subscribe(c, d) ==
    /\ d \notin subscribed[c]
    /\ subscribed' = [subscribed EXCEPT ![c] = @ \cup {d}]
    /\ awaiting_state' = [awaiting_state EXCEPT ![c] = @ \cup {d}]
    /\ UNCHANGED <<diagram_seq, buffered_seq, client_applied_seq, inflight_mutations>>

Mutate(author, d) ==
    /\ d \in subscribed[author]
    /\ d \notin awaiting_state[author]
    /\ diagram_seq[d] < MaxSeq
    /\ diagram_seq' = [diagram_seq EXCEPT ![d] = @ + 1]
    /\ LET new_seq == diagram_seq[d] + 1
           recipients == {c \in Clients : d \in subscribed[c] /\ c /= author}
       IN /\ inflight_mutations' = [c \in Clients |->
                 IF c \in recipients
                 THEN inflight_mutations[c] \cup {<<d, new_seq>>}
                 ELSE inflight_mutations[c]]
          /\ client_applied_seq' = [client_applied_seq EXCEPT ![author][d] = new_seq]
    /\ UNCHANGED <<subscribed, awaiting_state, buffered_seq>>

\* BUG: Does not check if seq > client_applied_seq before applying
ReceiveMutation(c, d, seq) ==
    /\ <<d, seq>> \in inflight_mutations[c]
    /\ inflight_mutations' = [inflight_mutations EXCEPT ![c] = @ \ {<<d, seq>>}]
    /\ IF d \in awaiting_state[c]
       THEN
           /\ buffered_seq' = [buffered_seq EXCEPT ![c][d] = @ \cup {seq}]
           /\ UNCHANGED client_applied_seq
       ELSE
           \* BUG: Blindly sets seq, even if it's older than current state!
           /\ client_applied_seq' = [client_applied_seq EXCEPT ![c][d] = seq]
           /\ UNCHANGED buffered_seq
    /\ UNCHANGED <<diagram_seq, subscribed, awaiting_state>>

ReceiveState(c, d) ==
    /\ d \in awaiting_state[c]
    /\ LET snapshot_seq == diagram_seq[d]
           buffered == buffered_seq[c][d]
           to_apply == {s \in buffered : s > snapshot_seq}
           final_seq == IF to_apply = {}
                        THEN snapshot_seq
                        ELSE snapshot_seq + Cardinality(to_apply)
       IN client_applied_seq' = [client_applied_seq EXCEPT ![c][d] = final_seq]
    /\ awaiting_state' = [awaiting_state EXCEPT ![c] = @ \ {d}]
    /\ buffered_seq' = [buffered_seq EXCEPT ![c][d] = {}]
    /\ UNCHANGED <<diagram_seq, subscribed, inflight_mutations>>

SubscribeAction == \E c \in Clients, d \in Diagrams: Subscribe(c, d)
MutateAction == \E c \in Clients, d \in Diagrams: Mutate(c, d)
ReceiveMutationAction == \E c \in Clients, d \in Diagrams, seq \in SeqRange: ReceiveMutation(c, d, seq)
ReceiveStateAction == \E c \in Clients, d \in Diagrams: ReceiveState(c, d)

Next ==
    \/ SubscribeAction
    \/ MutateAction
    \/ ReceiveMutationAction
    \/ ReceiveStateAction

Synced(c, d) ==
    /\ d \in subscribed[c]
    /\ d \notin awaiting_state[c]
    /\ ~\E m \in inflight_mutations[c]: m[1] = d

InvClientMatchesServer ==
    \A c \in Clients, d \in Diagrams:
        Synced(c, d) => client_applied_seq[c][d] = diagram_seq[d]

====
