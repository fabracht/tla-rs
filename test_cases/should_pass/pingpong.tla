---- MODULE pingpong -----------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

CONSTANT
   NumberOfClients
 , NumberOfPings

VARIABLES
   server_to_client
 , client_to_server
 , num_pings_sent
 , num_pongs_received

ClientIds == 1..NumberOfClients

vars == <<server_to_client, client_to_server, num_pings_sent, num_pongs_received>>

Data == [message: {"ping"}] \cup [message: {"pong"}]

ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

ServerSendPing ==
   /\ num_pings_sent < NumberOfPings
   /\ \E client_id \in ClientIds:
      ServerToClientChannel(client_id)!Send([message |-> "ping"])
   /\ num_pings_sent' = num_pings_sent + 1
   /\ UNCHANGED<<client_to_server, num_pongs_received>>

ServerHandlePong ==
   /\ \E client_id \in ClientIds:
      /\ ClientToServerChannel(client_id)!Recv([message |-> "pong"])
   /\ num_pongs_received' = num_pongs_received + 1
   /\ UNCHANGED<<server_to_client, num_pings_sent>>

ClientHandlePing(client_id) ==
   /\ ServerToClientChannel(client_id)!Recv([message |-> "ping"])
   /\ ClientToServerChannel(client_id)!Send([message |-> "pong"])
   /\ UNCHANGED<<num_pings_sent, num_pongs_received>>

Stutter == UNCHANGED<<vars>>

Next ==
   \/ ServerSendPing
   \/ ServerHandlePong
   \/ \E client_id \in ClientIds:
      ClientHandlePing(client_id)
   \/ Stutter

Init ==
   /\ server_to_client = [client_id \in ClientIds |-> ServerToClientChannel(client_id)!InitValue]
   /\ client_to_server = [client_id \in ClientIds |-> ClientToServerChannel(client_id)!InitValue]
   /\ num_pings_sent = 0
   /\ num_pongs_received = 0

TypeOK ==
   /\ num_pings_sent \in Nat
   /\ num_pongs_received \in Nat
   /\ \A client_id \in ClientIds:
      /\ ServerToClientChannel(client_id)!TypeOK
      /\ ClientToServerChannel(client_id)!TypeOK

Finished ==
   /\ num_pings_sent = num_pongs_received
   /\ num_pings_sent = NumberOfPings

NotFinished == \lnot Finished

================================================================================
