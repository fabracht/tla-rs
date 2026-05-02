---- MODULE FRListLin ----
EXTENDS Naturals

CONSTANTS NodeIds, Keys, Procs, HEAD, TAIL, HeadKey, TailKey

ASSUME HEAD \in NodeIds
ASSUME TAIL \in NodeIds
ASSUME HEAD # TAIL
ASSUME \A k \in Keys : HeadKey < k /\ k < TailKey

VARIABLES node, pc, op, dict

vars == <<node, pc, op, dict>>

NIL == "nil"

InitNode(k, r) == [exists |-> TRUE, key |-> k, right |-> r,
                   mark |-> 0, flag |-> 0, backlink |-> NIL]

EmptyNode == [exists |-> FALSE, key |-> 0, right |-> NIL,
              mark |-> 0, flag |-> 0, backlink |-> NIL]

NoOp == [kind |-> "none", key |-> 0, result |-> "none"]

Init ==
  /\ node = [n \in NodeIds |->
              IF n = HEAD THEN InitNode(HeadKey, TAIL)
              ELSE IF n = TAIL THEN InitNode(TailKey, NIL)
              ELSE EmptyNode]
  /\ pc = [p \in Procs |-> "idle"]
  /\ op = [p \in Procs |-> NoOp]
  /\ dict = {}

BeginInsert(p, k) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "running"]
  /\ op' = [op EXCEPT ![p] = [kind |-> "insert", key |-> k, result |-> "none"]]
  /\ UNCHANGED <<node, dict>>

BeginDelete(p, k) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "running"]
  /\ op' = [op EXCEPT ![p] = [kind |-> "delete", key |-> k, result |-> "none"]]
  /\ UNCHANGED <<node, dict>>

InsertCAS(p, prev, target, newId) ==
  /\ pc[p] = "running"
  /\ op[p].kind = "insert"
  /\ node[prev].exists
  /\ node[target].exists
  /\ ~node[newId].exists
  /\ prev # newId
  /\ target # newId
  /\ node[prev].right = target
  /\ node[prev].mark = 0
  /\ node[prev].flag = 0
  /\ node[prev].key < op[p].key
  /\ op[p].key < node[target].key
  /\ op[p].key \notin dict
  /\ node' = [node EXCEPT
                ![newId] = InitNode(op[p].key, target),
                ![prev] = [@ EXCEPT !.right = newId]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ op' = [op EXCEPT ![p] = [@ EXCEPT !.result = "ok"]]
  /\ dict' = dict \cup {op[p].key}

FlagCAS(prev, target) ==
  /\ prev # target
  /\ node[prev].exists
  /\ node[target].exists
  /\ node[target].key \in Keys
  /\ node[prev].right = target
  /\ node[prev].mark = 0
  /\ node[prev].flag = 0
  /\ node[target].mark = 0
  /\ node' = [node EXCEPT
                ![prev] = [@ EXCEPT !.flag = 1],
                ![target] = [@ EXCEPT !.backlink = prev]]
  /\ UNCHANGED <<pc, op, dict>>

MarkCAS(p, prev, target) ==
  /\ pc[p] = "running"
  /\ op[p].kind = "delete"
  /\ op[p].key = node[target].key
  /\ prev # target
  /\ node[prev].exists
  /\ node[target].exists
  /\ node[prev].right = target
  /\ node[prev].flag = 1
  /\ node[target].mark = 0
  /\ node[target].flag = 0
  /\ op[p].key \in dict
  /\ node' = [node EXCEPT
                ![target] = [@ EXCEPT !.mark = 1, !.backlink = prev]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ op' = [op EXCEPT ![p] = [@ EXCEPT !.result = "ok"]]
  /\ dict' = dict \ {op[p].key}

PhysDeleteCAS(prev, del) ==
  /\ prev # del
  /\ node[prev].exists
  /\ node[del].exists
  /\ node[prev].right = del
  /\ node[prev].flag = 1
  /\ node[del].mark = 1
  /\ node' = [node EXCEPT
                ![prev] = [@ EXCEPT !.right = node[del].right, !.flag = 0]]
  /\ UNCHANGED <<pc, op, dict>>

LinDuplicate(p) ==
  /\ pc[p] = "running"
  /\ op[p].kind = "insert"
  /\ op[p].key \in dict
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ op' = [op EXCEPT ![p] = [@ EXCEPT !.result = "duplicate"]]
  /\ UNCHANGED <<node, dict>>

LinNotFound(p) ==
  /\ pc[p] = "running"
  /\ op[p].kind = "delete"
  /\ op[p].key \notin dict
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ op' = [op EXCEPT ![p] = [@ EXCEPT !.result = "notfound"]]
  /\ UNCHANGED <<node, dict>>

Next ==
  \/ \E p \in Procs, k \in Keys : BeginInsert(p, k) \/ BeginDelete(p, k)
  \/ \E p \in Procs :
       \/ \E prev \in NodeIds, target \in NodeIds, newId \in NodeIds :
            InsertCAS(p, prev, target, newId)
       \/ \E prev \in NodeIds, target \in NodeIds : MarkCAS(p, prev, target)
       \/ LinDuplicate(p) \/ LinNotFound(p)
  \/ \E prev \in NodeIds, target \in NodeIds :
       FlagCAS(prev, target) \/ PhysDeleteCAS(prev, target)

RegularKeys ==
  {k \in Keys : \E n \in NodeIds :
                  node[n].exists /\ node[n].mark = 0 /\ node[n].key = k}

InvAbsConcrete == dict = RegularKeys

InvSorted ==
  \A n \in NodeIds :
    (node[n].exists /\ node[n].right \in NodeIds /\ node[node[n].right].exists)
      => node[n].key < node[node[n].right].key

InvNoMarkFlag ==
  \A n \in NodeIds :
    node[n].exists => ~(node[n].mark = 1 /\ node[n].flag = 1)

PhysicallyDeleted(n) ==
  /\ node[n].exists
  /\ node[n].mark = 1
  /\ \A k \in NodeIds : (node[k].exists /\ node[k].mark = 0) => node[k].right # n

InList(n) == node[n].exists /\ ~PhysicallyDeleted(n)

InvFlaggedPred ==
  \A n \in NodeIds, m \in NodeIds :
    (node[n].exists /\ node[m].exists
     /\ node[m].right = n /\ node[n].mark = 1 /\ node[m].mark = 0)
      => node[m].flag = 1

InvBacklink ==
  \A n \in NodeIds, m \in NodeIds :
    (node[n].exists /\ node[m].exists
     /\ node[n].mark = 1 /\ node[m].mark = 0 /\ node[m].right = n)
      => node[n].backlink = m

InvUniquePred ==
  \A n \in NodeIds, m1 \in NodeIds, m2 \in NodeIds :
    (InList(n) /\ InList(m1) /\ InList(m2)
     /\ node[m1].right = n /\ node[m2].right = n /\ m1 # m2)
      => FALSE

InvHasPred ==
  \A n \in NodeIds :
    (InList(n) /\ n # HEAD)
      => \E m \in NodeIds : InList(m) /\ node[m].right = n

InvHeadNoPred ==
  \A m \in NodeIds : node[m].exists => node[m].right # HEAD

ValidResult(p) ==
  \/ op[p].kind = "none"
  \/ op[p].kind = "insert" /\ op[p].result \in {"none", "ok", "duplicate"}
  \/ op[p].kind = "delete" /\ op[p].result \in {"none", "ok", "notfound"}

InvOpResult == \A p \in Procs : ValidResult(p)
====
