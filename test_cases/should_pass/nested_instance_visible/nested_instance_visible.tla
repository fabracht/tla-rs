---- MODULE nested_instance_visible ----
VARIABLE x
INSTANCE M2 WITH C <- 5
Init == x = 0
Next == UNCHANGED x
InvA == J!V = 5
====
