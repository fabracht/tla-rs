---- MODULE user_infix_ops ----
VARIABLES x

a \oplus b == a + b
a \odot b == a * b
a \ominus b == a - b

Init == x = 0
Next == x' = x

InvOplus == (3 \oplus 4) = 7
InvOdot == (3 \odot 4) = 12
InvOminus == (10 \ominus 3) = 7
InvLeftAssoc == (1 \oplus 2 \oplus 3) = 6
InvMixed == (2 \odot 3 \oplus 4) = 10
Inv == InvOplus /\ InvOdot /\ InvOminus /\ InvLeftAssoc /\ InvMixed
====
