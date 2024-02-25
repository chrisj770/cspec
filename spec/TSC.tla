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
       
TSCHandleBadMessage(tsc, msg, expectedState) == 
    IF tsc.state = "Canceled"
        THEN SendMessage(msg.pubkey, [type |-> "CANCELED", pubkey |-> tsc.pubkey])
    ELSE IF tsc.state = "Completed"
        THEN SendMessage(msg.pubkey, [type |-> "COMPLETED", pubkey |-> tsc.pubkey]) 
    ELSE IF tsc.state # expectedState
        THEN SendMessage(msg.pubkey, [type |-> "INVALID", pubkey |-> tsc.pubkey])
    ELSE FALSE  
    
TSCRemoveLastMessage(tsc, msg) == 
    TSCs' = {IF t.taskId = tsc.taskId
             THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
             ELSE t : t \in TSCs}
             
TSCConfirmTask_MessageFormat(msg) == 
    /\ msg.type = "CONFIRM_TASK"
    /\ IsWorker(msg.pubkey)

TSCConfirmTask_IsEnabled == 
    /\ \E t \in TSCs : \E msg \in t.msgs : TSCConfirmTask_MessageFormat(msg)

TSCConfirmTask_CanParticipate(msg, tsc) == 
    /\ Cardinality(tsc.participants) < tsc.numParticipants
    /\ tsc.checkQ[USSCGetReputation(msg.pubkey)]
    
TSCConfirmTask_AddParticipant(msg, tsc) == 
    /\ TSCs' = {IF t.taskId = tsc.taskId
                THEN [t EXCEPT !.msgs = t.msgs \ {msg}, 
                               !.participants = tsc.participants \union {msg.pubkey},
                               !.state = IF Cardinality(tsc.participants) + 1 = tsc.numParticipants
                                         THEN "Unavailable" ELSE "Available"]
                ELSE t : t \in TSCs}
                
TSCConfirmTask == 
    /\ TSCConfirmTask_IsEnabled
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : TSCConfirmTask_MessageFormat(msg)
           msg == CHOOSE m \in tsc.msgs : TSCConfirmTask_MessageFormat(m) 
       IN \/ /\ TSCHandleBadMessage(tsc, msg, "Available")
             /\ TSCRemoveLastMessage(tsc, msg)
          \/ /\ tsc.state = "Available"
             /\ IF TSCConfirmTask_CanParticipate(msg, tsc) 
                THEN /\ TSCConfirmTask_AddParticipant(msg, tsc)
                     /\ SendMessage(msg.pubkey, [type |-> "CONFIRM_SUCCESS", pubkey |-> tsc.pubkey])                    
                ELSE /\ TSCRemoveLastMessage(tsc, msg)
                     /\ SendMessage(msg.pubkey, [type |-> "CONFIRM_FAIL", pubkey |-> tsc.pubkey])
    /\ UNCHANGED <<Requesters, TSSC, USSC, USCs>>
    
TSCReceiveSubmitHash_MessageFormat(tsc, msg) == 
    /\ msg.type = "SUBMIT_HASH"
    /\ msg.pubkey \in tsc.participants

TSCReceiveSubmitHash_IsEnabled == 
    /\ \E t \in TSCs : \E msg \in t.msgs : TSCReceiveSubmitHash_MessageFormat(t, msg)

TSCAddHash(tsc, msg) ==  
    TSCs' = {IF t.taskId = tsc.taskId
             THEN [t EXCEPT !.msgs = t.msgs \ {msg},
                            !.hashes = t.hashes \union {msg.hash},
                            !.state = IF Cardinality(t.hashes)+1 = t.numParticipants
                                      THEN "QEvaluating"
                                      ELSE "Unavailable"]
             ELSE t: t \in TSCs}
    
TSCReceiveSubmitHash == 
    /\ TSCReceiveSubmitHash_IsEnabled
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : TSCReceiveSubmitHash_MessageFormat(t, msg)
           msg == CHOOSE m \in tsc.msgs : TSCReceiveSubmitHash_MessageFormat (tsc, m)
       IN \/ /\ TSCHandleBadMessage(tsc, msg, "Unavailable")
             /\ TSCRemoveLastMessage(tsc, msg)
          \/ /\ tsc.state = "Unavailable"
             /\ \/ /\ msg.hash \in tsc.hashes
                   /\ UNCHANGED <<TSCs>>
                \/ TSCAddHash(tsc, msg)
             /\ SendMessage(msg.pubkey, [type |-> "ACK", pubkey |-> tsc.pubkey])
    /\ UNCHANGED <<Requesters, TSSC, USSC, USCs>>

TSCReceiveQueryHashes_MessageFormat(tsc, msg) == 
    /\ msg.type = "QUERY_HASHES"
    /\ \/ /\ IsWorker(msg.pubkey)
          /\ Workers[GetWorker(msg.pubkey)].pubkey \in tsc.participants
       \/ /\ IsRequester(msg.pubkey)
          /\ msg.pubkey = tsc.owner

TSCReceiveQueryHashes_IsEnabled == 
    /\ \E t \in TSCs : /\ \E msg \in t.msgs : TSCReceiveQueryHashes_MessageFormat(t, msg)
                       /\ Cardinality(t.hashes) = t.numParticipants

TSCReceiveQueryHashes == 
    /\ TSCReceiveQueryHashes_IsEnabled
    /\ LET tsc == CHOOSE t \in TSCs : /\ \E msg \in t.msgs : TSCReceiveQueryHashes_MessageFormat(t, msg)
                                      /\ Cardinality(t.hashes) = t.numParticipants 
           msg == CHOOSE m \in tsc.msgs : TSCReceiveQueryHashes_MessageFormat(tsc, m)
       IN /\ \/ /\ TSCHandleBadMessage(tsc, msg, "QEvaluating") 
                /\ TSCRemoveLastMessage(tsc, msg)
             \/ /\ tsc.state = "QEvaluating"
                /\ TSCRemoveLastMessage(tsc, msg)
                /\ SendMessage(msg.pubkey, [type |-> "HASHES", pubkey |-> tsc.pubkey, hashes |-> tsc.hashes])
          /\ IF IsWorker(msg.pubkey) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<TSSC, USSC, USCs>>    

TSCNext == \/ /\ Cardinality(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ TSCConfirmTask
           \/ TSCReceiveSubmitHash
           \/ TSCReceiveQueryHashes

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 15:32:46 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
