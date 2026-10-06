---- MODULE Lib2 ----
Inner(F(_), v) == F(v)
Outer(A(_), k) == Inner(A, k)
====
