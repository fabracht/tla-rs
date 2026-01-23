VARIABLES x, s

Init == x = 1 ∧ s = {1, 2, 3}

Next == x ∈ {1, 2} ∧ x' = x + 1 ∧ s' = s

Inv1 == x ≤ 3
Inv2 == x ≠ 0
Inv3 == ¬(x = 100)
Inv4 == {1} ⊂ s
Inv5 == {1} ⊆ s
