---- MODULE bullet_implication ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
S == {1, 2}
Issue ==
    /\ x > 10
    /\ x < 20
    => x = 42
EquivList ==
    /\ x > 10
    /\ x < 20
    <=> x = 42
Quantified ==
    \A i \in S :
      /\ i > 10
      /\ x < 20
      => x = 42
ItemQuantifier ==
    /\ x > 5
    /\ \A i \in S : i > 0
    => x = 42
ItemIf ==
    /\ x > 5
    /\ IF x = 0 THEN TRUE ELSE TRUE
    => x = 42
ItemLet ==
    /\ x > 5
    /\ LET a == x IN a < 10
    => x = 42
LeftOfBullet ==
      /\ x > 10
      /\ x < 20
  => x = 42
OrOfAnds ==
    \/ /\ x > 10
       /\ x < 20
       => x = 42
    \/ FALSE
====
