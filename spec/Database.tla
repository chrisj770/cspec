------------------------------ MODULE Database ------------------------------
EXTENDS Common, TLC

TypeOK == TRUE

Init == Storage = [msgs |-> {}, 
                   data |-> {},
                     pk |-> [address |-> "STORAGE", type |-> "public_key"], 
                  state |-> "WORKING"]

(***************************************************************************)
(*                               SUBMIT_DATA                               *)
(***************************************************************************) 
ReceiveSubmitData_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_DATA" 
    /\ IsWorker(msg.from)

ReceiveSubmitData_IsEnabled == 
    /\ \E msg \in Storage.msgs : ReceiveSubmitData_MessageFormat(msg)
    
ReceiveSubmitData == 
    /\ ReceiveSubmitData_IsEnabled
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveSubmitData_MessageFormat(m)
           newData == [hash |-> ToString(NextUnique), 
                    address |-> msg.from, 
                 submission |-> msg.data]
           response == [type |-> "HASH", 
                        from |-> Storage.pk, 
                        hash |-> ToString(NextUnique)] 
       IN /\ Storage' = [Storage EXCEPT !.data = Storage.data \union {newData},
                                        !.msgs = Storage.msgs \ {msg}]
          /\ SendMessage(msg.from, response)
          /\ NextUnique' = NextUnique + 1
    /\ UNCHANGED <<Requesters>>

(***************************************************************************)
(*                                QUERY_DATA                               *)
(***************************************************************************) 
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
                            from |-> Storage.pk, 
                         allData |-> data] 
           IN IF IsWorker(msg.from)
              THEN /\ SendMessage(msg.from, response)
                   /\ UNCHANGED <<Requesters>> 
              ELSE /\ SendMessage(msg.from, response)
                   /\ UNCHANGED <<Workers>>
        /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \ {msg}]      
    /\ UNCHANGED <<NextUnique>>                                        

GlobalTimeout == 
    /\ Time >= MaxTime
    /\ Storage' = [Storage EXCEPT !.state = "TERMINATED"]
    /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, NextUnique>>
    
Terminating == /\ Storage.state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

Next == 
    \/ /\ Time < MaxTime
       /\ \/ ReceiveSubmitData
          \/ ReceiveQueryData
    \/ GlobalTimeout
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Sat Mar 02 12:22:43 CET 2024 by jungc
\* Created Sun Feb 25 10:53:35 CET 2024 by jungc
