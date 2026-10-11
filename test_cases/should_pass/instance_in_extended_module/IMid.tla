---- MODULE IMid ----
LOCAL INSTANCE IDouble
INSTANCE IStep
Grow(n) == Twice(Step(n))
====
