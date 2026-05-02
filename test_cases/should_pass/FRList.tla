---- MODULE FRList ----
EXTENDS Naturals

CONSTANTS NodeIds, Keys, HEAD, TAIL, HeadKey, TailKey

ASSUME HEAD \in NodeIds
ASSUME TAIL \in NodeIds
ASSUME HEAD # TAIL
ASSUME \A k \in Keys : HeadKey < k /\ k < TailKey

VARIABLE node

vars == <<node>>

NIL == "nil"

InitNode(k, r) == [exists |-> TRUE, key |-> k, right |-> r,
                   mark |-> 0, flag |-> 0, backlink |-> NIL]

EmptyNode == [exists |-> FALSE, key |-> 0, right |-> NIL,
              mark |-> 0, flag |-> 0, backlink |-> NIL]

Init ==
  node = [n \in NodeIds |->
            IF n = HEAD THEN InitNode(HeadKey, TAIL)
            ELSE IF n = TAIL THEN InitNode(TailKey, NIL)
            ELSE EmptyNode]

InsertCAS(k, prev, target, newId) ==
  /\ node[prev].exists
  /\ node[target].exists
  /\ ~node[newId].exists
  /\ prev # newId
  /\ target # newId
  /\ node[prev].right = target
  /\ node[prev].mark = 0
  /\ node[prev].flag = 0
  /\ node[prev].key < k
  /\ k < node[target].key
  /\ node' = [node EXCEPT
                ![newId] = InitNode(k, target),
                ![prev] = [@ EXCEPT !.right = newId]]

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

MarkCAS(prev, target) ==
  /\ prev # target
  /\ node[prev].exists
  /\ node[target].exists
  /\ node[prev].right = target
  /\ node[prev].flag = 1
  /\ node[target].mark = 0
  /\ node[target].flag = 0
  /\ node' = [node EXCEPT
                ![target] = [@ EXCEPT !.mark = 1, !.backlink = prev]]

PhysDeleteCAS(prev, del) ==
  /\ prev # del
  /\ node[prev].exists
  /\ node[del].exists
  /\ node[prev].right = del
  /\ node[prev].flag = 1
  /\ node[del].mark = 1
  /\ node' = [node EXCEPT
                ![prev] = [@ EXCEPT !.right = node[del].right, !.flag = 0]]

Next ==
  \/ \E k \in Keys :
       \E prev \in NodeIds, target \in NodeIds, newId \in NodeIds :
         InsertCAS(k, prev, target, newId)
  \/ \E prev \in NodeIds, target \in NodeIds :
       \/ FlagCAS(prev, target)
       \/ MarkCAS(prev, target)
       \/ PhysDeleteCAS(prev, target)

InvTypeOK ==
  \A n \in NodeIds :
    node[n].exists =>
      /\ node[n].mark \in {0, 1}
      /\ node[n].flag \in {0, 1}

InvNoMarkFlag ==
  \A n \in NodeIds :
    node[n].exists => ~(node[n].mark = 1 /\ node[n].flag = 1)

InvSorted ==
  \A n \in NodeIds :
    (node[n].exists /\ node[n].right \in NodeIds /\ node[node[n].right].exists)
      => node[n].key < node[node[n].right].key

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

PhysicallyDeleted(n) ==
  /\ node[n].exists
  /\ node[n].mark = 1
  /\ \A k \in NodeIds : (node[k].exists /\ node[k].mark = 0) => node[k].right # n

InList(n) == node[n].exists /\ ~PhysicallyDeleted(n)

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

InvNoDupKeys ==
  \A n1 \in NodeIds, n2 \in NodeIds :
    (node[n1].exists /\ node[n2].exists
     /\ node[n1].mark = 0 /\ node[n2].mark = 0
     /\ node[n1].key = node[n2].key /\ n1 # n2)
      => FALSE

====
