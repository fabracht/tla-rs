---- MODULE unbounded_choose ----
EXTENDS Naturals

VARIABLE x

Fresh(S) == CHOOSE v : v \notin S

Pick(e) == CHOOSE v : v = e

Init == x = 0

Next == \/ x' = Pick(42)
        \/ /\ Fresh({"a", "b"}) \notin {"a", "b"}
           /\ x' = 1

Inv ==
    /\ Fresh({1, 2, 3}) \notin {1, 2, 3}
    /\ Pick(7) = 7
    /\ Pick(<<1, 2>>) = <<1, 2>>
    /\ x \in {0, 1, 42}

====
