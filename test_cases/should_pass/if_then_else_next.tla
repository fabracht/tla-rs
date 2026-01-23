VARIABLES x

Init == x = 0

Next ==
    IF x < 5
    THEN x' = x + 1
    ELSE x' = 0

Inv == x <= 5
