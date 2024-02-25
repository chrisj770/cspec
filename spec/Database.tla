------------------------------ MODULE Database ------------------------------
EXTENDS Common 

TypeOK == TRUE

Init == Storage = [msgs |-> {}, 
                   data |-> {}]


ReceiveSubmitData_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_DATA" 
    /\ IsWorker(msg.pubkey)

ReceiveSubmitData_IsEnabled == 
    /\ \E msg \in Storage.msgs : ReceiveSubmitData_MessageFormat(msg)
    
ReceiveSubmitData == 
    /\ ReceiveSubmitData_IsEnabled
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveSubmitData_MessageFormat(m)
           hash == "Somehash"
           newData == [hash |-> hash, pubkey |-> msg.pubkey, data |-> msg.data]
           response == [type |-> "HASH", src |-> "STORAGE", hash |-> hash] 
           wid == CHOOSE i \in 1..NumWorkers : Workers[i].pubkey = msg.pubkey
       IN 
          /\ Storage' = [Storage EXCEPT !.data = Storage.data \union {newData},
                                        !.msgs = Storage.msgs \ {msg}]
          /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {response}]
    /\ UNCHANGED <<Requesters>>

ReceiveQueryData_MessageFormat(msg) == 
    /\ msg.type = "QUERY_DATA"
    /\ \/ IsWorker(msg.pubkey)
       \/ IsRequester(msg.pubkey)
    /\ \A h \in msg.hashes : \E struct \in Storage.data : struct.hash = h
    
ReceiveQueryData_IsEnabled == 
    /\ \E msg \in Storage.msgs : ReceiveQueryData_MessageFormat(msg)
    
ReceiveQueryData ==
    /\ ReceiveQueryData_IsEnabled
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveQueryData_MessageFormat(m) IN 
        /\ LET data == {d \in Storage.data : d.hash \in msg.hashes}
               response == [type |-> "DATA", src |-> "STORAGE", data |-> data] IN 
            /\ IF IsWorker(msg.pubkey)
               THEN LET i == GetWorker(msg.pubkey) IN
                    /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \union {response}]
                    /\ UNCHANGED <<Requesters>> 
               ELSE LET i == GetRequester(msg.pubkey) IN
                    /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \union {response}]
                    /\ UNCHANGED <<Workers>>
        /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \ {msg}]                                              

Next == 
    \/ ReceiveSubmitData
    \/ ReceiveQueryData

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 13:02:18 CET 2024 by jungc
\* Created Sun Feb 25 10:53:35 CET 2024 by jungc
