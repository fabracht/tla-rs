---- MODULE sync_simple ----
EXTENDS Integers

VARIABLES subscribed, has_pending

Init ==
    /\ subscribed = TRUE
    /\ has_pending = FALSE

SendMutation ==
    /\ subscribed = TRUE
    /\ has_pending' = TRUE
    /\ UNCHANGED subscribed

Unsubscribe ==
    /\ subscribed = TRUE
    /\ subscribed' = FALSE
    /\ UNCHANGED has_pending

Deliver ==
    /\ has_pending = TRUE
    /\ has_pending' = FALSE
    /\ UNCHANGED subscribed

Next ==
    \/ SendMutation
    \/ Unsubscribe
    \/ Deliver

\* This SHOULD be violated: pending while not subscribed
InvNoPendingWhileUnsubscribed ==
    has_pending => subscribed

====
