---- MODULE instance_definition_parse_error ----
VARIABLE x
H == INSTANCE Helpers
Init == x = H!Bad
Next == UNCHANGED x
====
