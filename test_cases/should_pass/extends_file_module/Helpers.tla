---- MODULE Helpers ----
EXTENDS Naturals

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b
Clamp(x, lo, hi) == Max(lo, Min(x, hi))
====
