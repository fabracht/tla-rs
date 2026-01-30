---- MODULE MQDBOwnershipTOCTOU_BugNoCAS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Users, Requests, DataValues

VARIABLES storage, reqPhase, reqSender, reqSnapshot, commitLog

vars == <<storage, reqPhase, reqSender, reqSnapshot, commitLog>>

Record == [owner : Users, data : DataValues]

Phases == {"idle", "reading", "checked", "rejected", "committed"}

Init ==
    /\ storage \in Record
    /\ reqPhase = [r \in Requests |-> "idle"]
    /\ reqSender = [r \in Requests |-> "none"]
    /\ reqSnapshot = [r \in Requests |-> "none"]
    /\ commitLog = {}

StartRequest(r) ==
    /\ reqPhase[r] = "idle"
    /\ \E u \in Users:
        /\ reqSender' = [reqSender EXCEPT ![r] = u]
        /\ reqPhase' = [reqPhase EXCEPT ![r] = "reading"]
    /\ UNCHANGED <<storage, reqSnapshot, commitLog>>

ReadStorage(r) ==
    /\ reqPhase[r] = "reading"
    /\ reqSnapshot' = [reqSnapshot EXCEPT ![r] = storage]
    /\ reqPhase' = [reqPhase EXCEPT ![r] = "snapshot_taken"]
    /\ UNCHANGED <<storage, reqSender, commitLog>>

CheckOwnership(r) ==
    /\ reqPhase[r] = "snapshot_taken"
    /\ reqSnapshot[r].owner = reqSender[r]
    /\ reqPhase' = [reqPhase EXCEPT ![r] = "checked"]
    /\ UNCHANGED <<storage, reqSender, reqSnapshot, commitLog>>

RejectNonOwner(r) ==
    /\ reqPhase[r] = "snapshot_taken"
    /\ reqSnapshot[r].owner # reqSender[r]
    /\ reqPhase' = [reqPhase EXCEPT ![r] = "rejected"]
    /\ UNCHANGED <<storage, reqSender, reqSnapshot, commitLog>>

Commit(r) ==
    /\ reqPhase[r] = "checked"
    /\ \E newData \in DataValues:
        /\ storage' = [storage EXCEPT !.data = newData]
        /\ commitLog' = commitLog \cup
            {[sender |-> reqSender[r], ownerAtCommit |-> storage.owner]}
    /\ reqPhase' = [reqPhase EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<reqSender, reqSnapshot>>

AdminTransfer(u) ==
    /\ storage.owner # u
    /\ storage' = [storage EXCEPT !.owner = u]
    /\ UNCHANGED <<reqPhase, reqSender, reqSnapshot, commitLog>>

Next ==
    \/ \E r \in Requests:
        \/ StartRequest(r)
        \/ ReadStorage(r)
        \/ CheckOwnership(r)
        \/ RejectNonOwner(r)
        \/ Commit(r)
    \/ \E u \in Users: AdminTransfer(u)

InvOwnershipSafety ==
    \A entry \in commitLog: entry.sender = entry.ownerAtCommit

TypeOK ==
    /\ storage \in Record
    /\ \A r \in Requests: reqPhase[r] \in Phases \cup {"snapshot_taken"}
    /\ \A r \in Requests: reqSender[r] \in Users \cup {"none"}
    /\ \A r \in Requests: reqSnapshot[r] \in Record \cup {"none"}

====
