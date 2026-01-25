---- MODULE tlc_operators ----
EXTENDS TLC

VARIABLES x

Init ==
    /\ x = 0
    /\ TLCSet(1, 42)
    /\ PrintT("Init complete")

Next ==
    /\ x < 3
    /\ x' = x + 1
    /\ PrintT(ToString(x'))

InvPrintT == PrintT(x) = TRUE

InvToString == ToString(123) = "123"

InvRandomElement == RandomElement({1, 2, 3}) \in {1, 2, 3}

InvAny == x \in Any

InvTLCGet == TLCGet(1) = 42

InvTLCGetLevel == TLCGet("level") >= 0

InvTLCGetDistinct == TLCGet("distinct") >= 1

InvTLCEval == TLCEval(1 + 2 + 3) = 6

====
