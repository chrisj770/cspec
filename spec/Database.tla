------------------------------ MODULE Database ------------------------------
EXTENDS Common 

TypeOK == TRUE

Init == Storage = [msgs |-> {}, 
                   data |-> {}]

ReceiveSubmitData_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_DATA" 
    /\ IsWorker(msg.from)

ReceiveSubmitData_IsEnabled == 
    /\ \E msg \in Storage.msgs : ReceiveSubmitData_MessageFormat(msg)
    
ReceiveSubmitData == 
    /\ ReceiveSubmitData_IsEnabled
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveSubmitData_MessageFormat(m)
           hash == "Somehash"
           newData == [hash |-> hash, 
                    address |-> msg.from, 
                 submission |-> msg.data]
           response == [type |-> "HASH", 
                        from |-> "STORAGE", 
                        hash |-> hash] 
       IN /\ Storage' = [Storage EXCEPT !.data = Storage.data \union {newData},
                                        !.msgs = Storage.msgs \ {msg}]
          /\ SendMessage(msg.from, response)
    /\ UNCHANGED <<Requesters>>

ReceiveQueryData_MessageFormat(msg) == 
    /\ msg.type = "QUERY_DATA"
    /\ \/ IsWorker(msg.from)
       \/ IsRequester(msg.from)
    /\ \A h \in msg.hashes : \E struct \in Storage.data : struct.hash = h
    
ReceiveQueryData_IsEnabled == 
    /\ \E msg \in Storage.msgs : ReceiveQueryData_MessageFormat(msg)
    
ReceiveQueryData ==
    /\ ReceiveQueryData_IsEnabled
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveQueryData_MessageFormat(m) IN 
        /\ LET data == {d \in Storage.data : d.hash \in msg.hashes}
               response == [type |-> "DATA", 
                            from |-> "STORAGE", 
                         allData |-> data] 
           IN IF IsWorker(msg.from)
              THEN /\ SendMessage(msg.from, response)
                   /\ UNCHANGED <<Requesters>> 
              ELSE /\ SendMessage(msg.from, response)
                   /\ UNCHANGED <<Workers>>
        /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \ {msg}]                                              

Next == 
    \/ ReceiveSubmitData
    \/ ReceiveQueryData

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 14:19:35 CET 2024 by jungc
\* Created Sun Feb 25 10:53:35 CET 2024 by jungc
