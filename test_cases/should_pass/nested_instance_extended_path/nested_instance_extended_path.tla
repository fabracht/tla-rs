---- MODULE nested_instance_extended_path ----
VARIABLE x
INSTANCE M
Init == x = 0
Next == UNCHANGED x
InvA == Val = 1
====
