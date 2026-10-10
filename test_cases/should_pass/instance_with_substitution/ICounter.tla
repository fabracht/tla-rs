---- MODULE ICounter ----
LOCAL INSTANCE Naturals
CONSTANT Limit
VARIABLE c
CInit == c = 0
CNext == c < Limit /\ c' = c + 1
CSpec == CInit /\ [][CNext]_c
Bounded == c \in 0..Limit /\ c \in Nat
====
