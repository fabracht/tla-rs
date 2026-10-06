---- MODULE instance_definition_parse_error ----
VARIABLE x
H == INSTANCE Helpers
Init == x = H!Good
Next == UNCHANGED x
====
