---- MODULE record_as_function ----

EXTENDS Naturals

VARIABLE x

rec == [one |-> 1, two |-> 2, three |-> 3]

Init == x = 0

Pick(r, k) == x' = r[k]

Next == \E k \in DOMAIN rec : Pick(rec, k)

Total ==
    LET sum[s \in SUBSET (DOMAIN rec)] ==
            IF s = {} THEN 0
            ELSE LET k == CHOOSE y \in s : TRUE
                 IN rec[k] + sum[s \ {k}]
    IN sum[DOMAIN rec]

InvDomain == DOMAIN rec = {"one", "two", "three"}

InvApply == rec["two"] = rec.two

InvRecursive == Total = 6

TypeOK == x \in 0..3

====
