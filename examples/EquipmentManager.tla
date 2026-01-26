---- MODULE EquipmentManager ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Serials, MaxTimestamp

VARIABLES
    taskQueue,
    activeSerials,
    metadataAtBroker,
    dataAtBroker,
    receivedMetadata,
    cachedTimestamp,
    subscribedToData,
    metadataTimerActive,
    requestSent

vars == <<taskQueue, activeSerials, metadataAtBroker, dataAtBroker,
          receivedMetadata, cachedTimestamp, subscribedToData,
          metadataTimerActive, requestSent>>

Timestamps == 1..MaxTimestamp

TaskMeta(s) == <<"meta", s>>

Init ==
    /\ taskQueue = <<>>
    /\ activeSerials = {}
    /\ metadataAtBroker = [s \in Serials |-> 0]
    /\ dataAtBroker = [s \in Serials |-> 0]
    /\ receivedMetadata = [s \in Serials |-> 0]
    /\ cachedTimestamp = [s \in Serials |-> 0]
    /\ subscribedToData = [s \in Serials |-> FALSE]
    /\ metadataTimerActive = [s \in Serials |-> FALSE]
    /\ requestSent = [s \in Serials |-> FALSE]

ManifestUpdate(s) ==
    /\ s \notin activeSerials
    /\ activeSerials' = activeSerials \union {s}
    /\ metadataTimerActive' = [metadataTimerActive EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<taskQueue, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, requestSent>>

CloudPublishesData(s) ==
    /\ \E ts \in Timestamps:
        /\ ts > dataAtBroker[s]
        /\ ts > metadataAtBroker[s]
        /\ dataAtBroker' = [dataAtBroker EXCEPT ![s] = ts]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>

CloudPublishesMetadata(s) ==
    /\ dataAtBroker[s] > metadataAtBroker[s]
    /\ metadataAtBroker' = [metadataAtBroker EXCEPT ![s] = dataAtBroker[s]]
    /\ UNCHANGED <<taskQueue, activeSerials, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>

ReceiveMetadata(s) ==
    /\ s \in activeSerials
    /\ metadataAtBroker[s] > 0
    /\ metadataAtBroker[s] > receivedMetadata[s]
    /\ metadataAtBroker[s] > cachedTimestamp[s]
    /\ receivedMetadata' = [receivedMetadata EXCEPT ![s] = metadataAtBroker[s]]
    /\ metadataTimerActive' = [metadataTimerActive EXCEPT ![s] = FALSE]
    /\ subscribedToData' = [subscribedToData EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, dataAtBroker,
                   cachedTimestamp, requestSent>>

ReceiveDataMatching(s) ==
    /\ s \in activeSerials
    /\ subscribedToData[s] = TRUE
    /\ dataAtBroker[s] = receivedMetadata[s]
    /\ receivedMetadata[s] > cachedTimestamp[s]
    /\ cachedTimestamp' = [cachedTimestamp EXCEPT ![s] = receivedMetadata[s]]
    /\ subscribedToData' = [subscribedToData EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<taskQueue, activeSerials, metadataAtBroker, dataAtBroker,
                   receivedMetadata, metadataTimerActive, requestSent>>

ReceiveDataStale(s) ==
    /\ s \in activeSerials
    /\ subscribedToData[s] = TRUE
    /\ dataAtBroker[s] < receivedMetadata[s]
    /\ UNCHANGED vars

MetadataTimeout(s) ==
    /\ s \in activeSerials
    /\ metadataTimerActive[s] = TRUE
    /\ metadataAtBroker[s] = 0
    /\ requestSent[s] = FALSE
    /\ taskQueue' = Append(taskQueue, TaskMeta(s))
    /\ requestSent' = [requestSent EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<activeSerials, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive>>

ProcessTask ==
    /\ Len(taskQueue) > 0
    /\ taskQueue' = Tail(taskQueue)
    /\ UNCHANGED <<activeSerials, metadataAtBroker, dataAtBroker, receivedMetadata,
                   cachedTimestamp, subscribedToData, metadataTimerActive, requestSent>>

Next ==
    \/ \E s \in Serials: ManifestUpdate(s)
    \/ \E s \in Serials: CloudPublishesData(s)
    \/ \E s \in Serials: CloudPublishesMetadata(s)
    \/ \E s \in Serials: ReceiveMetadata(s)
    \/ \E s \in Serials: ReceiveDataMatching(s)
    \/ \E s \in Serials: ReceiveDataStale(s)
    \/ \E s \in Serials: MetadataTimeout(s)
    \/ ProcessTask

TypeOK ==
    /\ taskQueue \in Seq({"meta"} \X Serials)
    /\ activeSerials \subseteq Serials
    /\ \A s \in Serials: metadataAtBroker[s] \in (0..MaxTimestamp)
    /\ \A s \in Serials: dataAtBroker[s] \in (0..MaxTimestamp)
    /\ \A s \in Serials: receivedMetadata[s] \in (0..MaxTimestamp)
    /\ \A s \in Serials: cachedTimestamp[s] \in (0..MaxTimestamp)
    /\ \A s \in Serials: subscribedToData[s] \in BOOLEAN
    /\ \A s \in Serials: metadataTimerActive[s] \in BOOLEAN
    /\ \A s \in Serials: requestSent[s] \in BOOLEAN

InvDataSubRequiresMetadata ==
    \A s \in Serials:
        subscribedToData[s] => (receivedMetadata[s] > cachedTimestamp[s])

InvCacheNotNewerThanReceived ==
    \A s \in Serials:
        cachedTimestamp[s] <= receivedMetadata[s]

InvReceivedNotNewerThanBroker ==
    \A s \in Serials:
        receivedMetadata[s] <= metadataAtBroker[s]

InvDataSubOnlyWhenActive ==
    \A s \in Serials:
        subscribedToData[s] => (s \in activeSerials)

InvTimersOnlyWhenActive ==
    \A s \in Serials:
        metadataTimerActive[s] => (s \in activeSerials)

InvMetadataNotNewerThanData ==
    \A s \in Serials:
        metadataAtBroker[s] <= dataAtBroker[s]

Fairness ==
    /\ WF_vars(ProcessTask)
    /\ \A s \in Serials: WF_vars(MetadataTimeout(s))
    /\ \A s \in Serials: WF_vars(ReceiveMetadata(s))
    /\ \A s \in Serials: WF_vars(ReceiveDataMatching(s))
    /\ \A s \in Serials: WF_vars(CloudPublishesData(s))
    /\ \A s \in Serials: WF_vars(CloudPublishesMetadata(s))

OptionsEventuallyArrive ==
    \A s \in Serials:
        (s \in activeSerials /\ receivedMetadata[s] > 0) ~>
        (cachedTimestamp[s] = receivedMetadata[s])

Spec == Init /\ [][Next]_vars /\ Fairness
====
