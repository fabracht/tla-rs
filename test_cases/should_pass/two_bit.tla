VARIABLES lo, hi

Init == lo = 0 /\ hi = 0

Next ==
    \/ (lo < 1 /\ lo' = lo + 1 /\ hi' = hi)
    \/ (lo = 1 /\ lo' = 0 /\ hi' = hi + 1 /\ hi < 1)

InvLo == lo <= 1
InvHi == hi <= 1
