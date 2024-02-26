-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, USSC, TLC, Common 

CONSTANT TaskPostDeadline
ASSUME TaskPostDeadline >= RegistrationDeadline

TypeOK == TRUE

Init == 
    TSCs = [msgs |-> {},
           tasks |-> {}]  
           
HandleBadMessage(task, msg, expectedState) == 
    IF task.state = "Canceled"
        THEN SendMessage(msg.pubkey, [type |-> "CANCELED", pubkey |-> "TSC"])
    ELSE IF task.state = "Completed"
        THEN SendMessage(msg.pubkey, [type |-> "COMPLETED", pubkey |-> "TSC"]) 
    ELSE IF task.state # expectedState
        THEN SendMessage(msg.pubkey, [type |-> "INVALID", pubkey |-> "TSC"])
    ELSE FALSE  
           
AddFields(struct, owner) == 
    struct @@ [taskId |-> Cardinality(TSCs.tasks) + struct.id,
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
               hashes |-> {}]
                   
ReceivePostTasks_MessageFormat(msg) == 
    /\ msg.type = "POST_TASKS"
    /\ IsRequester(msg.pubkey)

ReceivePostTasks_IsEnabled == 
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    
PostTasks(msg) == 
    LET addTSCs == {AddFields(t, msg.pubkey) : t \in msg.tasks} 
    IN /\ TSCs' = [TSCs EXCEPT !.tasks = TSCs.tasks \union addTSCs,
                               !.msgs = TSCs.msgs \ {msg}]
       /\ NextPubkey' = NextPubkey + Cardinality(addTSCs) 

ReceivePostTasks == 
    /\ ReceivePostTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN IF Time < TaskPostDeadline 
          THEN /\ PostTasks(msg)
               /\ SendMessage(msg.pubkey, [type |-> "ACK", pubkey |-> "TSC"])                                  
          ELSE /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
               /\ SendMessage(msg.pubkey, [type |-> "INVALID", pubkey |-> "TSC"])
               /\ UNCHANGED <<NextPubkey>>
    /\ UNCHANGED <<Workers, USSC, USCs>>

ReceiveQueryTasks_MessageFormat(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ \/ /\ IsRequester(msg.pubkey)
          /\ msg.owner # NULL
          /\ \A t \in TSCs.tasks : t.owner = msg.owner => t.state = "Unavailable"
       \/ /\ IsWorker(msg.pubkey)
          /\ msg.owner = NULL

ReceiveQueryTasks_IsEnabled == 
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
           valid == Time >= TaskPostDeadline
           matchingTSCs == IF ~valid THEN NULL 
                           ELSE IF IsWorker(msg.pubkey) THEN TSCs.tasks
                                ELSE {t \in TSCs.tasks : t.owner = msg.owner} 
           response == [type |-> IF valid THEN "TASKS" ELSE "INVALID",  
                       pubkey |-> "TSC", 
                       tasks |-> matchingTSCs]
       IN /\ SendMessage(msg.pubkey, response)
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          /\ IF IsRequester(msg.pubkey) 
             THEN UNCHANGED <<Workers>>
             ELSE UNCHANGED <<Requesters>> 
    /\ UNCHANGED <<USSC, USCs, NextPubkey>>           
             
ReceiveConfirmTask_MessageFormat(msg) == 
    /\ msg.type = "CONFIRM_TASK"
    /\ IsWorker(msg.pubkey)
    /\ \E t \in TSCs.tasks : msg.task = t.pubkey

ReceiveConfirmTask_IsEnabled == 
    /\ \E msg \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(msg)

CanParticipate(msg, task) == 
    /\ Cardinality(task.participants) < task.numParticipants
    /\ task.checkQ[USSCGetReputation(msg.pubkey)]
    
AddParticipant(msg, tsc) == 
    /\ TSCs' = [TSCs EXCEPT 
                !.msgs = TSCs.msgs \ {msg},
                !.tasks = {IF t.taskId = tsc.taskId
                           THEN [t EXCEPT !.participants = t.participants \union {msg.pubkey},
                                          !.state = IF Cardinality(t.participants) + 1 = t.numParticipants
                                                    THEN "Unavailable" ELSE "Available"]
                           ELSE t : t \in TSCs.tasks}]
                
ReceiveConfirmTask == 
    /\ ReceiveConfirmTask_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(m) 
           tsc == CHOOSE t \in TSCs.tasks : msg.task = t.pubkey
       IN \/ /\ HandleBadMessage(tsc, msg, "Available")
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Available"
             /\ IF CanParticipate(msg, tsc) 
                THEN /\ AddParticipant(msg, tsc)
                     /\ SendMessage(msg.pubkey, [type |-> "CONFIRM_SUCCESS", pubkey |-> "TSC", task |-> tsc.pubkey])                    
                ELSE /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
                     /\ SendMessage(msg.pubkey, [type |-> "CONFIRM_FAIL", pubkey |-> "TSC", task |-> tsc.pubkey])
    /\ UNCHANGED <<Requesters, USSC, USCs, NextPubkey>>
    
    
ReceiveSubmitHash_TaskFormat(t, msg) == 
    /\ msg.task = t.pubkey
    /\ msg.pubkey \in t.participants 

ReceiveSubmitHash_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_HASH"
    /\ msg.task \in {t.pubkey : t \in TSCs.tasks}
    /\ \E t \in TSCs.tasks : ReceiveSubmitHash_TaskFormat(t, msg)

ReceiveSubmitHash_IsEnabled == 
    /\ \E msg \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(msg)

SubmitHash(tsc, msg) ==  
    TSCs' = [TSCs EXCEPT 
                !.msgs = TSCs.msgs \ {msg},
                !.tasks = {IF t.taskId = tsc.taskId
                           THEN [t EXCEPT !.hashes = t.hashes \union {msg.hash},
                                          !.state = IF Cardinality(t.hashes)+1 = t.numParticipants
                                                    THEN "QEvaluating"
                                                    ELSE "Unavailable"]
                           ELSE t: t \in TSCs.tasks}]
    
ReceiveSubmitHash == 
    /\ ReceiveSubmitHash_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveSubmitHash_TaskFormat(t, msg)
       IN \/ /\ HandleBadMessage(tsc, msg, "Unavailable")
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Unavailable"
             /\ \/ /\ msg.hash \in tsc.hashes
                   /\ UNCHANGED <<TSCs>>
                \/ SubmitHash(tsc, msg)
             /\ SendMessage(msg.pubkey, [type |-> "ACK", pubkey |-> "TSC", task |-> tsc.pubkey])
    /\ UNCHANGED <<Requesters, USSC, USCs, NextPubkey>>
    
ReceiveQueryHashes_TaskFormat(t, msg) == 
    /\ Cardinality(t.participants) = t.numParticipants
    /\ \/ /\ IsWorker(msg.pubkey)
          /\ Workers[GetWorker(msg.pubkey)].pubkey \in t.participants
       \/ /\ IsRequester(msg.pubkey)
          /\ msg.pubkey = t.owner

ReceiveQueryHashes_MessageFormat(msg) == 
    /\ msg.type = "QUERY_HASHES"
    /\ \E t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)

ReceiveQueryHashes_IsEnabled == 
    /\ \E msg \in TSCs.msgs : /\ ReceiveQueryHashes_MessageFormat(msg)
    
ReceiveQueryHashes == 
    /\ ReceiveQueryHashes_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryHashes_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)
       IN /\ \/ /\ HandleBadMessage(tsc, msg, "QEvaluating") 
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             \/ /\ tsc.state = "QEvaluating"
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
                /\ SendMessage(msg.pubkey, [type |-> "HASHES", pubkey |-> "TSC", task |-> tsc.pubkey, hashes |-> tsc.hashes])
          /\ IF IsWorker(msg.pubkey) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USSC, USCs, NextPubkey>>    

Next == 
    \/ ReceivePostTasks
    \/ ReceiveQueryTasks
    \/ ReceiveConfirmTask
    \/ ReceiveSubmitHash
    \/ ReceiveQueryHashes

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 09:06:16 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
