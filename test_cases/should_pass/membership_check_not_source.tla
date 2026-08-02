---- MODULE membership_check_not_source ----

EXTENDS Naturals, Sequences

VARIABLE x

Init == x = <<1>>

Next == x' = <<1>> /\ x' \in Seq({1, 2})

InvT == x \in Seq({1, 2})

====
