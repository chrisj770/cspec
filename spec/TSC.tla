-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, USSC, TLC, Common 

TSCTypeOK == TRUE

TSCInit == TSCs = {}

GetIndex(task, allTasks) == 
    CHOOSE i \in DOMAIN allTasks : allTasks[i] = task
    
AddFields(struct, owner) == 
    struct @@ [taskId |-> Cardinality(TSCs) + struct.id,
               pubkey |-> ToString(NextPubkey + struct.id-1),
               category |-> "PlaceholderCategory",
               state |-> "Available",
               owner |-> owner,
               participants |-> {},
               numParticipants |-> 1,
               globalReputationThreshold |-> 0,
               expertiseReputationThreshold |-> 0,
               checkQ |-> [j \in 0..1 |-> TRUE],
               QEvaluate |-> [j \in 0..1 |-> TRUE],
               hashes |-> {},
               msgs |-> {}]

TSCPostTasks(tasks, owner) == 
    LET addTSCs == {AddFields(t, owner) : t \in tasks} 
    IN /\ TSCs' = TSCs \union addTSCs
       /\ NextPubkey' = NextPubkey + Cardinality(tasks) 
    
TSCSendResponse(pubkey, message) == 
    \/ /\ USSCCheckUser(pubkey, "REQUESTER")
       /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = pubkey IN
            /\ Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
       /\ UNCHANGED <<Workers>>
    \/ /\ USSCCheckUser(pubkey, "WORKER")
       /\ LET wid == CHOOSE key \in DOMAIN Workers : Workers[key].pubkey = pubkey IN
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
       /\ UNCHANGED <<Requesters>>
       
TSCHandleBadMessage(tsc, msg, expectedState) == 
    IF tsc.state = "Canceled"
        THEN TSCSendResponse(msg.pubkey, [type |-> "CANCELED", pubkey |-> tsc.pubkey])
    ELSE IF tsc.state = "Completed"
        THEN TSCSendResponse(msg.pubkey, [type |-> "COMPLETED", pubkey |-> tsc.pubkey]) 
    ELSE IF tsc.state # expectedState
        THEN TSCSendResponse(msg.pubkey, [type |-> "INVALID", pubkey |-> tsc.pubkey])
    ELSE FALSE  
    
TSCRemoveLastMessage(tsc, msg) == 
    TSCs' = {IF t.taskId = tsc.taskId
             THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
             ELSE t : t \in TSCs}

TSCConfirmTask_CanParticipate(msg, tsc) == 
    /\ Cardinality(tsc.participants) < tsc.numParticipants
    /\ tsc.checkQ[USSCGetUser(msg.pubkey, "WORKER").info.reputation]
    
TSCConfirmTask_AddParticipant(msg, tsc) == 
    /\ TSCs' = {IF t.taskId = tsc.taskId
                THEN [t EXCEPT !.msgs = t.msgs \ {msg}, 
                               !.participants = tsc.participants \union {USSCGetUser(msg.pubkey, "WORKER").info.pubkey},
                               !.state = IF Cardinality(tsc.participants) + 1 = tsc.numParticipants
                                         THEN "Unavailable" ELSE "Available"]
                ELSE t : t \in TSCs}
                
TSCConfirmTask == 
    /\ \E t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK"
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK" IN 
        /\ LET msg == CHOOSE m \in tsc.msgs : m.type = "CONFIRM_TASK" IN 
            /\ USSCCheckUser(msg.pubkey, "WORKER")
            /\ \/ /\ TSCHandleBadMessage(tsc, msg, "Available")
                  /\ TSCRemoveLastMessage(tsc, msg)
               \/ /\ tsc.state = "Available"
                  /\ IF TSCConfirmTask_CanParticipate(msg, tsc) 
                     THEN /\ TSCConfirmTask_AddParticipant(msg, tsc)
                          /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_SUCCESS", pubkey |-> tsc.pubkey])                    
                     ELSE /\ TSCRemoveLastMessage(tsc, msg)
                          /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_FAIL", pubkey |-> tsc.pubkey])
    /\ UNCHANGED <<TSSC, USSC, USCs>>
    
TSCAddHash(tsc, msg) ==  
    /\ TSCs' = {IF t.taskId = tsc.taskId
                THEN [t EXCEPT !.msgs = t.msgs \ {msg},
                               !.hashes = t.hashes \union {msg.hash},
                               !.state = IF Cardinality(t.hashes)+1 = t.numParticipants
                                         THEN "QEvaluating"
                                         ELSE "Unavailable"]
                ELSE t : t \in TSCs}
    
TSCReceiveSubmitHash == 
    /\ \E t \in TSCs : \E msg \in t.msgs : /\ msg.type = "SUBMIT_HASH"
                                           /\ msg.pubkey \in t.participants
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : /\ msg.type = "SUBMIT_HASH" 
                                                          /\ msg.pubkey \in t.participants IN 
        /\ LET msg == CHOOSE m \in tsc.msgs : /\ m.type = "SUBMIT_HASH" 
                                              /\ m.pubkey \in tsc.participants IN 
            /\ USSCCheckUser(msg.pubkey, "WORKER")
            /\ \/ /\ TSCHandleBadMessage(tsc, msg, "Unavailable")
                  /\ TSCRemoveLastMessage(tsc, msg)
               \/ /\ tsc.state = "Unavailable"
                  /\ \/ /\ msg.hash \in tsc.hashes
                        /\ UNCHANGED <<TSCs>>
                     \/ TSCAddHash(tsc, msg)
                  /\ TSCSendResponse(msg.pubkey, [type |-> "ACK", pubkey |-> tsc.pubkey])
    /\ UNCHANGED <<Requesters, TSSC, USSC, USCs>>
    

TSCReceiveQueryHashes == 
    /\ \E t \in TSCs : /\ \E msg \in t.msgs : /\ msg.type = "QUERY_HASHES"
                                              /\ msg.pubkey = t.owner
                       /\ Cardinality(t.hashes) = t.numParticipants
    /\ LET tsc == CHOOSE t \in TSCs : /\ \E msg \in t.msgs : /\ msg.type = "QUERY_HASHES"
                                                             /\ msg.pubkey = t.owner
                                      /\ Cardinality(t.hashes) = t.numParticipants IN 
        /\ LET msg == CHOOSE m \in tsc.msgs : /\ m.type = "QUERY_HASHES"
                                              /\ m.pubkey = tsc.owner IN 
            \/ /\ \/ USSCCheckUser(msg.pubkey, "REQUESTER")
                  \/ USSCCheckUser(msg.pubkey, "WORKER")
               /\ \/ /\ TSCHandleBadMessage(tsc, msg, "QEvaluating") 
                     /\ TSCRemoveLastMessage(tsc, msg)
                  \/ /\ tsc.state = "QEvaluating"
                     /\ TSCRemoveLastMessage(tsc, msg)
                     /\ TSCSendResponse(msg.pubkey, [type |-> "HASHES", pubkey |-> tsc.pubkey, hashes |-> tsc.hashes])
    /\ UNCHANGED <<TSSC, USSC, USCs>>    

TSCNext == \/ /\ Cardinality(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ TSCConfirmTask
           \/ TSCReceiveSubmitHash
           \/ TSCReceiveQueryHashes
            \* \/ TSCUnavailable(tsc)
            \* \/ TSCQEvaluating(tsc)

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 11:49:07 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
