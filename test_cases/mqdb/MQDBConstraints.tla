---- MODULE MQDBConstraints ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ids, Fields, FieldValues

VARIABLES store, unique_fields, not_null_fields, fk_restrict, fk_cascade, fk_set_null

vars == <<store, unique_fields, not_null_fields, fk_restrict, fk_cascade, fk_set_null>>

NullVal == "null"

AllFK == fk_restrict \cup fk_cascade \cup fk_set_null

Init ==
    /\ store = [i \in Ids |-> [f \in Fields |-> NullVal]]
    /\ unique_fields = {}
    /\ not_null_fields = {}
    /\ fk_restrict = {}
    /\ fk_cascade = {}
    /\ fk_set_null = {}

Exists(id) == \E f \in Fields : store[id][f] # NullVal

FKTargetExists(val) ==
    val = NullVal \/ (val \in Ids /\ Exists(val))

UniqueOk(data, uf) ==
    data[uf] = NullVal \/ \A oid \in Ids : (~Exists(oid) \/ store[oid][uf] # data[uf])

UniqueOkForUpdate(id, field, val) ==
    val = NullVal \/ \A oid \in Ids : (oid = id \/ ~Exists(oid) \/ store[oid][field] # val)

HasRestrictRef(id, excluded) ==
    \E oid \in Ids : (oid \notin excluded /\ Exists(oid) /\ \E fk \in fk_restrict : store[oid][fk] = id)

DirectCascadeRefs(S) ==
    S \cup {oid \in Ids : Exists(oid) /\ \E fk \in fk_cascade : store[oid][fk] \in S}

CascadeSet(id) ==
    LET s0 == {id}
        s1 == DirectCascadeRefs(s0)
        s2 == DirectCascadeRefs(s1)
    IN s2

AddUniqueConstraint(field) ==
    /\ field \notin unique_fields
    /\ \A id1 \in Ids : \A id2 \in Ids :
        ((Exists(id1) /\ Exists(id2) /\ id1 # id2 /\ store[id1][field] # NullVal)
            => store[id1][field] # store[id2][field])
    /\ unique_fields' = unique_fields \cup {field}
    /\ UNCHANGED <<store, not_null_fields, fk_restrict, fk_cascade, fk_set_null>>

AddNotNull(field) ==
    /\ field \notin not_null_fields
    /\ \A i \in Ids : (Exists(i) => store[i][field] # NullVal)
    /\ not_null_fields' = not_null_fields \cup {field}
    /\ UNCHANGED <<store, unique_fields, fk_restrict, fk_cascade, fk_set_null>>

FKSafeToAdd(field) ==
    \A i \in Ids : (Exists(i) => FKTargetExists(store[i][field]))

AddFKRestrict(field) ==
    /\ field \notin AllFK
    /\ FKSafeToAdd(field)
    /\ fk_restrict' = fk_restrict \cup {field}
    /\ UNCHANGED <<store, unique_fields, not_null_fields, fk_cascade, fk_set_null>>

AddFKCascade(field) ==
    /\ field \notin AllFK
    /\ FKSafeToAdd(field)
    /\ fk_cascade' = fk_cascade \cup {field}
    /\ UNCHANGED <<store, unique_fields, not_null_fields, fk_restrict, fk_set_null>>

AddFKSetNull(field) ==
    /\ field \notin AllFK
    /\ FKSafeToAdd(field)
    /\ fk_set_null' = fk_set_null \cup {field}
    /\ UNCHANGED <<store, unique_fields, not_null_fields, fk_restrict, fk_cascade>>

ValidCreate(id, data) ==
    /\ ~Exists(id)
    /\ \A f \in not_null_fields : data[f] # NullVal
    /\ \A uf \in unique_fields : UniqueOk(data, uf)
    /\ \A fk \in AllFK : FKTargetExists(data[fk])
    /\ store' = [store EXCEPT ![id] = data]
    /\ UNCHANGED <<unique_fields, not_null_fields, fk_restrict, fk_cascade, fk_set_null>>

ValidDelete(id) ==
    LET to_delete == CascadeSet(id)
    IN
    /\ Exists(id)
    /\ ~\E did \in to_delete : HasRestrictRef(did, to_delete)
    /\ store' = [oid \in Ids |->
        IF oid \in to_delete
        THEN [f \in Fields |-> NullVal]
        ELSE [f \in Fields |->
            IF f \in fk_set_null /\ store[oid][f] \in to_delete
            THEN NullVal
            ELSE store[oid][f]]]
    /\ UNCHANGED <<unique_fields, not_null_fields, fk_restrict, fk_cascade, fk_set_null>>

ValidUpdate(id, field, val) ==
    /\ Exists(id)
    /\ val # NullVal
    /\ \A uf \in unique_fields : (uf # field \/ UniqueOkForUpdate(id, field, val))
    /\ (field \in AllFK) => FKTargetExists(val)
    /\ store' = [store EXCEPT ![id] = [@ EXCEPT ![field] = val]]
    /\ UNCHANGED <<unique_fields, not_null_fields, fk_restrict, fk_cascade, fk_set_null>>

Next ==
    \/ \E f \in Fields : AddUniqueConstraint(f)
    \/ \E f \in Fields : AddNotNull(f)
    \/ \E f \in Fields : AddFKRestrict(f)
    \/ \E f \in Fields : AddFKCascade(f)
    \/ \E f \in Fields : AddFKSetNull(f)
    \/ \E i \in Ids, data \in [Fields -> FieldValues \cup {NullVal}] : ValidCreate(i, data)
    \/ \E i \in Ids : ValidDelete(i)
    \/ \E i \in Ids, f \in Fields, v \in FieldValues : ValidUpdate(i, f, v)

InvUniqueConstraint ==
    \A uf \in unique_fields :
        \A id1 \in Ids : \A id2 \in Ids :
            ((Exists(id1) /\ Exists(id2) /\ id1 # id2 /\ store[id1][uf] # NullVal)
                => store[id1][uf] # store[id2][uf])

InvNotNullIntegrity ==
    \A f \in not_null_fields :
        \A i \in Ids :
            (Exists(i) => store[i][f] # NullVal)

InvFKIntegrity ==
    \A fk \in AllFK :
        \A i \in Ids :
            (Exists(i) => FKTargetExists(store[i][fk]))

====
