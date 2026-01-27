--------------------------- MODULE enabled_bench ---------------------------
VARIABLES x, y, turn

Init == x = 0 /\ y = 0 /\ turn = "x"

IncX == /\ turn = "x"
        /\ x < 5
        /\ x' = x + 1
        /\ y' = y
        /\ turn' = "y"

IncY == /\ turn = "y"
        /\ y < 5
        /\ y' = y + 1
        /\ x' = x
        /\ turn' = "x"

ResetX == /\ turn = "x"
          /\ x >= 3
          /\ x' = 0
          /\ y' = y
          /\ turn' = "y"

ResetY == /\ turn = "y"
          /\ y >= 3
          /\ y' = 0
          /\ x' = x
          /\ turn' = "x"

Next == IncX \/ IncY \/ ResetX \/ ResetY

InvEnabled == ENABLED(IncX) \/ ENABLED(IncY) \/ ENABLED(ResetX) \/ ENABLED(ResetY)

=============================================================================
