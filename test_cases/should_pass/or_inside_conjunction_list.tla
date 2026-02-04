VARIABLES x, y

Init ==
    /\ x = 0
    /\ y = 0

Step1 ==
    /\ x = 0 \/ x = 1
    /\ x' = x + 1
    /\ y' = y

Step2 ==
    /\ y = 0 \/ y = 1
    /\ y' = y + 1
    /\ x' = x

Next == Step1 \/ Step2

InvBound == x <= 3 /\ y <= 3
