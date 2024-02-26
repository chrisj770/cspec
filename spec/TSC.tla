-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

CONSTANT TaskPostDeadline

TypeOK == TRUE

Init == 
    TSCs = [state |-> "WORKING",
             msgs |-> {},
               pk |-> [address |-> "TSC", type |-> "public_key"],
            tasks |-> {}]  
           
HandleBadMessage(task, msg, expectedState) == 
    IF task.state = "Canceled"
        THEN SendMessage(msg.from, [type |-> "CANCELED", from |-> TSCs.pk])
    ELSE IF task.state = "Completed"
        THEN SendMessage(msg.from, [type |-> "COMPLETED", from |-> TSCs.pk]) 
    ELSE IF task.state # expectedState
        THEN SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk])
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
    /\ IsRequester(msg.from)

ReceivePostTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    
PostTasks(msg) == 
    LET addTSCs == {AddFields(t, msg.from) : t \in msg.tasks} 
    IN /\ TSCs' = [TSCs EXCEPT !.tasks = TSCs.tasks \union addTSCs,
                               !.msgs = TSCs.msgs \ {msg}]
       /\ NextPubkey' = NextPubkey + Cardinality(addTSCs) 

ReceivePostTasks == 
    /\ ReceivePostTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN IF Time < TaskPostDeadline 
          THEN /\ PostTasks(msg)
               /\ SendMessage(msg.from, [type |-> "ACK", from |-> TSCs.pk])                                  
          ELSE /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
               /\ SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk])
               /\ UNCHANGED <<NextPubkey>>
    /\ UNCHANGED <<Workers, USCs>>

ReceiveQueryTasks_MessageFormat(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ \/ /\ IsRequester(msg.from)
          /\ msg.owner # NULL
          /\ \A t \in TSCs.tasks : t.owner = msg.owner => t.state = "Unavailable"
       \/ /\ IsWorker(msg.from)
          /\ msg.owner = NULL

ReceiveQueryTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
           valid == Time >= TaskPostDeadline
           matchingTSCs == IF ~valid THEN NULL 
                           ELSE IF IsWorker(msg.from) THEN TSCs.tasks
                                ELSE {t \in TSCs.tasks : t.owner = msg.owner} 
           response == [type |-> IF valid THEN "TASKS" ELSE "INVALID",  
                        from |-> TSCs.pk, 
                       tasks |-> matchingTSCs]
       IN /\ SendMessage(msg.from, response)
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          /\ IF IsRequester(msg.from) 
             THEN UNCHANGED <<Workers>>
             ELSE UNCHANGED <<Requesters>> 
    /\ UNCHANGED <<USCs, NextPubkey>>           
             
ReceiveConfirmTask_MessageFormat(msg) == 
    /\ msg.type = "CONFIRM_TASK"
    /\ IsWorker(msg.from)
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
                                from |-> TSCs.pk, 
                                user |-> msg.from, 
                                task |-> msg.task]
                IN /\ SendMessage(USCs.pk, request) 
                   /\ TSCs' = [TSCs EXCEPT !.state = "CHECK_REPUTATION", 
                                           !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, NextPubkey>>
    
CheckReputation_MessageFormat(msg) == 
    /\ msg.type \in {"REPUTATION", "NOT_REGISTERED"}
    /\ msg.from = USCs.pk
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
           response == [from |-> TSCs.pk, task |-> tsc.address]
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
    /\ msg.from \in t.participants 

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
             /\ SendMessage(msg.from, [type |-> "ACK", 
                                       from |-> TSCs.pk, 
                                       task |-> tsc.address])
    /\ UNCHANGED <<Requesters, USCs, NextPubkey>>
    
ReceiveQueryHashes_TaskFormat(t, msg) == 
    /\ Cardinality(t.participants) = t.numParticipants
    /\ \/ /\ IsWorker(msg.from)
          /\ Workers[GetWorker(msg.from)].pk \in t.participants
       \/ /\ IsRequester(msg.from)
          /\ msg.from = t.owner

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
                /\ SendMessage(msg.from, [type |-> "HASHES", 
                                          from |-> TSCs.pk, 
                                          task |-> tsc.address, 
                                        hashes |-> tsc.hashes])
          /\ IF IsWorker(msg.from) 
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
\* Last modified Mon Feb 26 13:57:47 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
