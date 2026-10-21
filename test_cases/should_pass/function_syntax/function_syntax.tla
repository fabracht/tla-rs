---- MODULE function_syntax ----
EXTENDS Naturals
VARIABLE x
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]
add[a \in 0..3, b \in 0..3] == IF b = 0 THEN a ELSE add[a, b - 1] + 1
f2 == [a \in 1..2, b \in 1..2 |-> a + b]
g == [p \in (1..2) \X (1..2) |-> p[1] + p[2]]
h == [a, b \in 1..2 |-> a * b]
k == [a \in {1}, <<b, c>> \in {<<2, 3>>} |-> a + b + c]
m == [a \in {1} \X {2}, b \in {3} |-> a[1] + a[2] + b]
step[s \in 0..2, t \in 0..2] == s + t
gx[n \in 0..3] == n + x
ApplyAt4(f) == f[4]
Probe(f) == \A j \in {100} : f[1] = 6
Init == x = 0
Next == x < 2 /\ x' = step[x, 1] /\ (fact[x])' > 0 /\ (gx[1])' = x' + 1
InvFact == fact[4] = 24 /\ fact[0] = 1
InvAdd == add[2, 3] = 5
InvF2 == f2[1, 2] = 3 /\ f2[<<2, 2>>] = 4 /\ DOMAIN f2 = (1..2) \X (1..2)
InvG == g[1, 2] = 3
InvH == h[2, 2] = 4 /\ DOMAIN h = (1..2) \X (1..2)
InvK == k[1, <<2, 3>>] = 6
InvM == m[<<1, 2>>, 3] = 6 /\ DOMAIN m = ({1} \X {2}) \X {3}
InvLet == LET s[a \in 0..2, b \in 0..2] == a * b IN s[2, 2] = 4
InvExcept == [f2 EXCEPT ![1, 1] = 10][1, 1] = 10 /\ [f2 EXCEPT ![1, 1] = 10][2, 2] = 4
InvState == x = 2 \/ f2[x + 1, 1] = x + 2
InvPassed == ApplyAt4(fact) = 24
InvDeep == LET d[n \in 0..500] == IF n = 0 THEN 0 ELSE d[n - 1] + 1 IN d[500] = 500
InvCapture == \A j \in {5} : LET cg[i \in {1}] == i + j IN Probe(cg)
InvProduct == <<<<1, 2>>, 3>> \in ({1} \X {2}) \X {3} /\ <<1, 2, 3>> \in {1} \X {2} \X {3} /\ <<1, <<2, 3>>>> \in {1} \X ({2} \X {3})
====
