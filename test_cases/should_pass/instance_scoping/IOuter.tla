---- MODULE IOuter ----
EXTENDS Naturals
CONSTANT K
Base == 5
LOCAL INSTANCE IInner WITH c <- Base
UsesInner == F(1)
Offset(p) == p + Base
Fold(op(_, _), a, b) == op(a, b)
Scaled == K * 2
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
UsesNested == FromInner
====
