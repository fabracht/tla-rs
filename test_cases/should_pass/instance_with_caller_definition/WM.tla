---- MODULE WM ----
EXTENDS Naturals
CONSTANT c
VARIABLE y
Foo == 2
Bar == 2
RECURSIVE Val(_)
Val(a) == 2
g[i \in 1..2] == 2
a \oplus b == a + b
Sum == 1 \oplus 1
Get == c
Set(a) == y' = a
====
