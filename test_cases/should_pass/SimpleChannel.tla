---- MODULE SimpleChannel ----
EXTENDS Naturals, Sequences

VARIABLE buffer

TypeOK == TRUE

InitValue == <<>>

Send(msg) ==
    buffer' = Append(buffer, msg)

Recv ==
    /\ Len(buffer) > 0
    /\ buffer' = Tail(buffer)

Init == buffer = <<>>
Next == Send("msg") \/ Recv

====
