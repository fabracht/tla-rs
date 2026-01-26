---- MODULE enabled_operator ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Inc == x' = x + 1 /\ x < 3
Dec == x' = x - 1 /\ x > 0

Next == Inc \/ Dec

CanInc == ENABLED Inc
CanDec == ENABLED Dec

InvAtZero == (x = 0) => (~CanDec /\ CanInc)
InvAtThree == (x = 3) => (CanDec /\ ~CanInc)
InvMiddle == (x > 0 /\ x < 3) => (CanDec /\ CanInc)

====
