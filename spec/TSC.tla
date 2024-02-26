-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

CONSTANT TaskPostDeadline

TypeOK == TRUE

Init == 
    TSCs = [state |-> "WORKING",
           msgs |-> {},
           tasks |-> {}]  
           
HandleBadMessage(task, msg, expectedState) == 
    IF task.state = "Canceled"
        THEN SendMessage(msg.address, [type |-> "CANCELED", address |-> "TSC"])
    ELSE IF task.state = "Completed"
        THEN SendMessage(msg.address, [type |-> "COMPLETED", address |-> "TSC"]) 
    ELSE IF task.state # expectedState
        THEN SendMessage(msg.address, [type |-> "INVALID", address |-> "TSC"])
    ELSE FALSE  
           
AddFields(struct, owner) == 
    struct @@ [taskId |-> Cardinality(TSCs.tasks) + struct.id,
               address |-> ToString(NextPubkey + struct.id-1),
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
    /\ IsRequester(msg.address)

ReceivePostTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    
PostTasks(msg) == 
    LET addTSCs == {AddFields(t, msg.address) : t \in msg.tasks} 
    IN /\ TSCs' = [TSCs EXCEPT !.tasks = TSCs.tasks \union addTSCs,
                               !.msgs = TSCs.msgs \ {msg}]
       /\ NextPubkey' = NextPubkey + Cardinality(addTSCs) 

ReceivePostTasks == 
    /\ ReceivePostTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN IF Time < TaskPostDeadline 
          THEN /\ PostTasks(msg)
               /\ SendMessage(msg.address, [type |-> "ACK", address |-> "TSC"])                                  
          ELSE /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
               /\ SendMessage(msg.address, [type |-> "INVALID", address |-> "TSC"])
               /\ UNCHANGED <<NextPubkey>>
    /\ UNCHANGED <<Workers, USCs>>

ReceiveQueryTasks_MessageFormat(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ \/ /\ IsRequester(msg.address)
          /\ msg.owner # NULL
          /\ \A t \in TSCs.tasks : t.owner = msg.owner => t.state = "Unavailable"
       \/ /\ IsWorker(msg.address)
          /\ msg.owner = NULL

ReceiveQueryTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
           valid == Time >= TaskPostDeadline
           matchingTSCs == IF ~valid THEN NULL 
                           ELSE IF IsWorker(msg.address) THEN TSCs.tasks
                                ELSE {t \in TSCs.tasks : t.owner = msg.owner} 
           response == [type |-> IF valid THEN "TASKS" ELSE "INVALID",  
                       address |-> "TSC", 
                       tasks |-> matchingTSCs]
       IN /\ SendMessage(msg.address, response)
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          /\ IF IsRequester(msg.address) 
             THEN UNCHANGED <<Workers>>
             ELSE UNCHANGED <<Requesters>> 
    /\ UNCHANGED <<USCs, NextPubkey>>           
             
ReceiveConfirmTask_MessageFormat(msg) == 
    /\ msg.type = "CONFIRM_TASK"
    /\ IsWorker(msg.address)
    /\ \E t \in TSCs.tasks : msg.task = t.address

ReceiveConfirmTask_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(msg)
                
ReceiveConfirmTask == 
    /\ ReceiveConfirmTask_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(m) 
           tsc == CHOOSE t \in TSCs.tasks : msg.task = t.address
       IN \/ /\ HandleBadMessage(tsc, msg, "Available")
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             /\ UNCHANGED <<USCs>>
          \/ /\ tsc.state = "Available"
             /\ Cardinality(tsc.participants) < tsc.numParticipants
             /\ LET request == [type |-> "GET_REPUTATION", 
                               address |-> "TSC", 
                               user |-> msg.address, 
                               task |-> msg.task]
                IN /\ SendMessage("USC", request) 
                   /\ TSCs' = [TSCs EXCEPT !.state = "CHECK_REPUTATION", 
                                           !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, NextPubkey>>
    
CheckReputation_MessageFormat(msg) == 
    /\ msg.type \in {"REPUTATION", "NOT_REGISTERED"}
    /\ msg.address = "USC"
    /\ \A f \in {"reputation", "user", "task"} : f \in DOMAIN msg
    
CheckReputation_IsEnabled == 
    /\ TSCs.state = "CHECK_REPUTATION"
    /\ \E msg \in TSCs.msgs : CheckReputation_MessageFormat(msg)

CanParticipate(reputation, task) == 
    /\ Cardinality(task.participants) < task.numParticipants
    /\ task.checkQ[reputation]
    
AddParticipant(msg, tsc) == 
    /\ TSCs' = [TSCs EXCEPT 
                !.state = "WORKING",
                !.msgs = TSCs.msgs \ {msg},
                !.tasks = {IF t.taskId = tsc.taskId
                           THEN [t EXCEPT !.participants = t.participants \union {msg.user},
                                          !.state = IF Cardinality(t.participants) + 1 = t.numParticipants
                                                    THEN "Unavailable" ELSE "Available"]
                           ELSE t : t \in TSCs.tasks}]
    
CheckReputation == 
    /\ CheckReputation_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : CheckReputation_MessageFormat(m) 
           tsc == CHOOSE t \in TSCs.tasks : t.address = msg.task
           response == [address |-> "TSC", task |-> tsc.address]
       IN IF msg.type = "REPUTATION"
          THEN IF CanParticipate(msg.reputation, tsc)  
               THEN /\ AddParticipant(msg, tsc)
                    /\ SendMessage(msg.user, [type |-> "CONFIRM_SUCCESS"] @@ response)                    
               ELSE /\ SendMessage(msg.user, [type |-> "CONFIRM_FAIL"] @@ response)
                    /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                            !.state = "WORKING"]
          ELSE /\ SendMessage(msg.user, [type |-> "NOT_REGISTERED"] @@ response)
               /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                       !.state = "WORKING"]
    /\ UNCHANGED <<Requesters, USCs, NextPubkey>>

ReceiveSubmitHash_TaskFormat(t, msg) == 
    /\ msg.task = t.address
    /\ msg.address \in t.participants 

ReceiveSubmitHash_MessageFormat(msg) == 
    /\ msg.type = "SUBMIT_HASH"
    /\ msg.task \in {t.address : t \in TSCs.tasks}
    /\ \E t \in TSCs.tasks : ReceiveSubmitHash_TaskFormat(t, msg)

ReceiveSubmitHash_IsEnabled == 
    /\ TSCs.state = "WORKING"
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
             /\ SendMessage(msg.address, [type |-> "ACK", address |-> "TSC", task |-> tsc.address])
    /\ UNCHANGED <<Requesters, USCs, NextPubkey>>
    
ReceiveQueryHashes_TaskFormat(t, msg) == 
    /\ Cardinality(t.participants) = t.numParticipants
    /\ \/ /\ IsWorker(msg.address)
          /\ Workers[GetWorker(msg.address)].address \in t.participants
       \/ /\ IsRequester(msg.address)
          /\ msg.address = t.owner

ReceiveQueryHashes_MessageFormat(msg) == 
    /\ msg.type = "QUERY_HASHES"
    /\ \E t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)

ReceiveQueryHashes_IsEnabled ==
    /\ TSCs.state = "WORKING" 
    /\ \E msg \in TSCs.msgs : /\ ReceiveQueryHashes_MessageFormat(msg)
    
ReceiveQueryHashes == 
    /\ ReceiveQueryHashes_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryHashes_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)
       IN /\ \/ /\ HandleBadMessage(tsc, msg, "QEvaluating") 
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             \/ /\ tsc.state = "QEvaluating"
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
                /\ SendMessage(msg.address, [type |-> "HASHES", address |-> "TSC", task |-> tsc.address, hashes |-> tsc.hashes])
          /\ IF IsWorker(msg.address) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextPubkey>>    

Next == 
    \/ ReceivePostTasks
    \/ ReceiveQueryTasks
    \/ ReceiveConfirmTask
    \/ ReceiveSubmitHash
    \/ ReceiveQueryHashes
    \/ CheckReputation

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 11:08:31 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
