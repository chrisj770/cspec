------------------------------ MODULE Database ------------------------------
EXTENDS FiniteSets, Common, TLC

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init == Storage = [msgs |-> {}, 
                   data |-> {},
                     pk |-> [address |-> "STORAGE", type |-> "public_key"], 
                  state |-> "WORKING"]

(***************************************************************************)
(*                               SUBMIT_DATA                               *)
(*                                                                         *) 
(* Receive "SUBMIT_DATA" message from Worker containing encrypted sensory  *)
(* data. Upon receipt, generate a new unique "hash" and persist the data,  *)
(* then send "HASH" message to Worker containing the hash.                 *)
(***************************************************************************) 
ReceiveSubmitData_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_DATA" 

ReceiveSubmitData_IsEnabled == 
    /\ Storage.state = "WORKING"
        
ReceiveSubmitData == 
    /\ ReceiveSubmitData_IsEnabled
    /\ \E msg \in Storage.msgs : ReceiveSubmitData_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveSubmitData_MessageFormat(m)
           newData == [hash |-> ToString(NextUnique), 
                    address |-> msg.from, 
                 submission |-> msg.data]
           response == [type |-> "HASH", 
                        from |-> Storage.pk, 
                        hash |-> ToString(NextUnique)] 
       IN /\ Storage' = [Storage EXCEPT !.data = Storage.data \union {newData},
                                        !.msgs = Storage.msgs \ {msg}]
          /\ SendWorkerMessage(msg.from, response)
          /\ NextUnique' = NextUnique + 1
    /\ UNCHANGED <<Requesters>>

(***************************************************************************)
(*                                QUERY_DATA                               *)
(*                                                                         *)
(* Receive "QUERY_DATA" message from Worker/Requester containing a list of *)
(* hashes for which to request encrypted data. Upon receipt, send "DATA"   *)
(* message with the corresponding data to the Worker/Requester.            *)
(***************************************************************************) 
ReceiveQueryData_MessageFormat(msg) == 
    /\ msg.type = "QUERY_DATA"
    /\ \A h \in msg.hashes : \E struct \in Storage.data : struct.hash = h
    
ReceiveQueryData_IsEnabled == 
    /\ Storage.state = "WORKING"
    
ReceiveQueryData ==
    /\ ReceiveQueryData_IsEnabled
    /\ \E msg \in Storage.msgs : ReceiveQueryData_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in Storage.msgs : ReceiveQueryData_MessageFormat(m) IN 
        /\ LET data == {d \in Storage.data : d.hash \in msg.hashes}
               response == [type |-> "DATA", 
                            from |-> Storage.pk, 
                         allData |-> data] 
           IN \/ /\ SendWorkerMessage(msg.from, response)
                 /\ UNCHANGED <<Requesters>> 
              \/ /\ SendRequesterMessage(msg.from, response)
                 /\ UNCHANGED <<Workers>>
        /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \ {msg}]      
    /\ UNCHANGED <<NextUnique>>                                        

(***************************************************************************)
(* Terminating: Allows Storage to remain working indefinitely, required by *)
(* TLA+ for stuttering.                                                    *)
(***************************************************************************) 
Terminating == /\ Storage.state = "WORKING"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

(***************************************************************************)
(*                            ACTION DEFINITIONS                           *)
(***************************************************************************)
Next == 
    \/ ReceiveSubmitData
    \/ ReceiveQueryData
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Wed Mar 20 09:56:19 CET 2024 by jungc
\* Created Sun Feb 25 10:53:35 CET 2024 by jungc
