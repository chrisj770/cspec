-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

TypeOK == TRUE

Init == TSCs = [state |-> "WORKING",
                 msgs |-> {},
                   pk |-> [address |-> "TSC", type |-> "public_key"],
                tasks |-> {},
     TaskPostDeadline |-> FALSE]  
           
HandleStateMismatch(task, msg, expectedState) == 
    IF task.state = "Canceled"
        THEN SendMessage(msg.from, [type |-> "CANCELED", from |-> TSCs.pk, task |-> task.address])
    ELSE IF task.state = "Completed"
        THEN SendMessage(msg.from, [type |-> "COMPLETED", from |-> TSCs.pk, task |-> task.address]) 
    ELSE IF task.state # expectedState
        THEN SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk, task |-> task.address])
    ELSE FALSE  
    
AddFields(struct, owner, taskId, address) == 
              struct @@ [taskId |-> taskId,
                        address |-> ToString(address),
                       category |-> "PlaceholderCategory",
                          state |-> "Available",
                          owner |-> owner,
                   participants |-> {},
      globalReputationThreshold |-> 0,
   expertiseReputationThreshold |-> 0,
                         checkQ |-> [j \in 0..1 |-> TRUE],
                      QEvaluate |-> [j \in 0..1 |-> TRUE],
                         hashes |-> {}, 
               requesterWeights |-> NULL,
                  workerWeights |-> {}]
    
GetWorkerTSC(t) == [Sd |-> t.Sd, 
                    Pd |-> t.Pd, 
                    Td |-> t.Td, 
               address |-> t.address, 
                taskId |-> t.taskId, 
                 owner |-> t.owner, 
       numParticipants |-> t.numParticipants, 
              category |-> t.category,
                 state |-> t.state] 

GetUpdatedTasks == 
    {[t EXCEPT !.state = IF \/ /\ t.Sd
                               /\ t.state \in {"Pending", "Available", "Unavailable"}
                            \/ /\ t.Pd
                               /\ t.state \in {"Pending", "Available", "Unavailable", "QEvaluating"} 
                         THEN "Canceled"
                         ELSE t.state]: t \in TSCs.tasks}

(***************************************************************************)
(*                             RECV_POST_TASKS                             *)
(***************************************************************************)                 
ReceivePostTasks_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "tasks"} : f \in DOMAIN msg
    /\ IsRequester(msg.from)
    /\ msg.type = "POST_TASKS"

ReceivePostTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    
RECURSIVE PostTasks(_, _, _)
PostTasks(tasksToAdd, addedTasks, msg) == 
    \/ /\ tasksToAdd = <<>>
       /\ TSCs' = [TSCs EXCEPT !.tasks = TSCs.tasks \union addedTasks,
                               !.msgs = TSCs.msgs \ {msg} ]
       /\ NextUnique' = NextUnique + Cardinality(addedTasks)
    \/ /\ Len(tasksToAdd) > 0
       /\ LET nextTask == Head(tasksToAdd) 
              nextTaskId == Cardinality(TSCs.tasks) + Cardinality(addedTasks) + 1
              nextAddress == NextUnique + Cardinality(addedTasks)
              newTaskList == addedTasks \union {AddFields(nextTask, msg.from, nextTaskId, nextAddress)} 
          IN PostTasks(Tail(tasksToAdd), newTaskList, msg) 

ReceivePostTasks == 
    /\ ReceivePostTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN IF ~TSCs.TaskPostDeadline 
          THEN /\ PostTasks(msg.tasks, {}, msg)
               /\ SendMessage(msg.from, [type |-> "ACK", from |-> TSCs.pk])                                  
          ELSE /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
               /\ SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk])
               /\ UNCHANGED <<NextUnique>>
    /\ UNCHANGED <<Workers, USCs>>

(***************************************************************************)
(*                             RECV_QUERY_TASKS                            *)
(***************************************************************************)
ReceiveQueryTasks_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "owner"} : f \in DOMAIN msg
    /\ msg.type = "QUERY_TASKS" 
    /\ IF IsRequester(msg.from)
       THEN /\ msg.owner # NULL
       ELSE IF IsWorker(msg.from) 
            THEN msg.owner = NULL
            ELSE FALSE 

ReceiveQueryTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)
    
ReceiveQueryTasks_SendTasks(tasks, msg) == 
    LET matchingTSCs == IF IsWorker(msg.from) THEN tasks 
                        ELSE {t \in tasks : t.owner = msg.owner} 
        tscData == IF IsWorker(msg.from) 
                   THEN {GetWorkerTSC(t) : t \in matchingTSCs}
                   ELSE matchingTSCs
        response == [type |-> "TASKS",  
                     from |-> TSCs.pk, 
                    tasks |-> tscData]
    IN SendMessage(msg.from, response)

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
           updatedTasks == GetUpdatedTasks
       IN /\ IF TSCs.TaskPostDeadline
             THEN ReceiveQueryTasks_SendTasks(updatedTasks, msg)
             ELSE SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk])
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                  !.tasks = updatedTasks]
          /\ IF IsRequester(msg.from) 
             THEN UNCHANGED <<Workers>>
             ELSE UNCHANGED <<Requesters>> 
    /\ UNCHANGED <<USCs, NextUnique>>           

(***************************************************************************)
(*                            RECV_CONFIRM_TASK                            *)
(***************************************************************************)
ReceiveConfirmTask_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ IsWorker(msg.from)
    /\ msg.type = "CONFIRM_TASK"
    /\ \E t \in TSCs.tasks : msg.task = t.address

ReceiveConfirmTask_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(msg)
                
ReceiveConfirmTask == 
    /\ ReceiveConfirmTask_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(m) 
           updatedTasks == GetUpdatedTasks
           tsc == CHOOSE t \in updatedTasks : msg.task = t.address
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN \/ /\ msg.from \in tsc.participants
             /\ SendMessage(msg.from, response @@ [type |-> "CONFIRM_SUCCESS"])
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                     !.tasks = updatedTasks]
             /\ UNCHANGED <<USCs>>
          \/ /\ ~(msg.from \in tsc.participants)
             /\ \/ /\ tsc.state \in {"Unavailable", "QEvaluating"}
                   /\ SendMessage(msg.from, response @@ [type |-> "CONFIRM_FAIL"])
                \/ /\ tsc.state = "Canceled"
                   /\ SendMessage(msg.from, response @@ [type |-> "CANCELED"])
                \/ /\ tsc.state = "Completed"
                   /\ SendMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                     !.tasks = updatedTasks]
             /\ UNCHANGED <<USCs>>
          \/ /\ ~(msg.from \in tsc.participants)
             /\ tsc.state = "Available"
             /\ LET request == [type |-> "GET_REPUTATION", 
                                from |-> TSCs.pk, 
                                user |-> msg.from, 
                                task |-> msg.task]
                IN /\ SendMessage(USCs.pk, request) 
                   /\ TSCs' = [TSCs EXCEPT !.state = "CHECK_REPUTATION", 
                                           !.msgs = TSCs.msgs \ {msg}, 
                                           !.tasks = updatedTasks]
             /\ UNCHANGED <<Workers>>
    /\ UNCHANGED <<Requesters, NextUnique>>
    
(***************************************************************************)
(*                            CHECK_REPUTATION                             *)
(***************************************************************************)
CheckReputation_MessageFormat(msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = USCs.pk
    /\ msg.type \in {"REPUTATION", "NOT_REGISTERED"}
    /\ msg.type = "REPUTATION" => \A f \in {"reputation", "user", "task"} : 
                                     f \in DOMAIN msg
    
CheckReputation_IsEnabled == 
    /\ TSCs.state = "CHECK_REPUTATION"
    /\ \E msg \in TSCs.msgs : CheckReputation_MessageFormat(msg)

CanParticipate(reputation, task) == 
    /\ task.state \notin {"Canceled", "Completed"}
    /\ Cardinality(task.participants) < task.numParticipants
    /\ task.checkQ[reputation]
    
AddParticipant(taskSet, msg, taskId) == 
    LET newTaskList == {[t EXCEPT 
        !.participants = IF t.taskId = taskId THEN t.participants \union {msg.user} ELSE t.participants,
        !.state = IF t.taskId = taskId
                  THEN IF Cardinality(t.participants) + 1 = t.numParticipants
                       THEN "Unavailable"
                       ELSE "Available"
                  ELSE t.state] : t \in taskSet}
    IN TSCs' = [TSCs EXCEPT !.state = "WORKING",
                            !.msgs = TSCs.msgs \ {msg},
                            !.tasks = newTaskList]
    
CheckReputation == 
    /\ CheckReputation_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : CheckReputation_MessageFormat(m) 
           updatedTasks == GetUpdatedTasks
           tsc == CHOOSE t \in updatedTasks : t.address = msg.task
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN IF msg.type = "REPUTATION"
          THEN IF CanParticipate(msg.reputation, tsc)  
               THEN /\ SendMessage(msg.user, [type |-> "CONFIRM_SUCCESS"] @@ response)
                    /\ AddParticipant(updatedTasks, msg, tsc.taskId)
               ELSE /\ SendMessage(msg.user, [type |-> "CONFIRM_FAIL"] @@ response)
                    /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                            !.state = "WORKING", 
                                            !.tasks = updatedTasks]
          ELSE /\ SendMessage(msg.user, [type |-> "NOT_REGISTERED"] @@ response)
               /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                       !.state = "WORKING", 
                                       !.tasks = updatedTasks]
    /\ UNCHANGED <<Requesters, USCs, NextUnique>>

(***************************************************************************)
(*                            RECV_SUBMIT_HASH                             *)
(***************************************************************************)
ReceiveSubmitHash_TaskFormat(t, msg) == 
    /\ msg.task = t.address
    /\ msg.from \in t.participants 

ReceiveSubmitHash_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "hash", "task"} : f \in DOMAIN msg
    /\ msg.type = "SUBMIT_HASH"
    /\ msg.task \in {t.address : t \in TSCs.tasks}
    /\ \E t \in TSCs.tasks : ReceiveSubmitHash_TaskFormat(t, msg)

ReceiveSubmitHash_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(msg)

SubmitHash(taskSet, msg, taskId) ==  
    LET newTaskSet == {[t EXCEPT 
        !.hashes = IF t.taskId = taskId THEN t.hashes \union {msg.hash} ELSE t.hashes,
        !.state = IF t.taskId = taskId 
                  THEN IF Cardinality(t.hashes)+1 = t.numParticipants 
                       THEN "QEvaluating"
                       ELSE "Unavailable"
                  ELSE t.state] : t \in taskSet}
    IN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                            !.tasks = newTaskSet] 
    
ReceiveSubmitHash == 
    /\ ReceiveSubmitHash_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(m)
           updatedTasks == GetUpdatedTasks
           tsc == CHOOSE t \in updatedTasks : ReceiveSubmitHash_TaskFormat(t, msg)
       IN \/ /\ HandleStateMismatch(tsc, msg, "Unavailable")
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                     !.tasks = updatedTasks]
          \/ /\ tsc.state = "Unavailable"
             /\ \/ /\ msg.hash \in tsc.hashes
                   /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                           !.tasks = updatedTasks]
                \/ SubmitHash(updatedTasks, msg, tsc.taskId)
             /\ SendMessage(msg.from, [type |-> "ACK", 
                                       from |-> TSCs.pk, 
                                       task |-> tsc.address])
    /\ UNCHANGED <<Requesters, USCs, NextUnique>>

(***************************************************************************)
(*                            RECV_QUERY_HASHES                            *)
(***************************************************************************)
ReceiveQueryHashes_TaskFormat(t, msg) == 
    IF IsWorker(msg.from)
    THEN Workers[GetWorker(msg.from)].pk \in t.participants
    ELSE IF IsRequester(msg.from)
         THEN msg.from = t.owner
         ELSE FALSE

ReceiveQueryHashes_MessageFormat(msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ \/ IsWorker(msg.from)
       \/ IsRequester(msg.from)
    /\ msg.type = "QUERY_HASHES"
    /\ \E t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)

ReceiveQueryHashes_IsEnabled ==
    /\ TSCs.state = "WORKING" 
    /\ \E msg \in TSCs.msgs : /\ ReceiveQueryHashes_MessageFormat(msg)
    
ReceiveQueryHashes == 
    /\ ReceiveQueryHashes_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryHashes_MessageFormat(m)
           updatedTasks == GetUpdatedTasks
           tsc == CHOOSE t \in updatedTasks : ReceiveQueryHashes_TaskFormat(t, msg)
       IN /\ \/ HandleStateMismatch(tsc, msg, "QEvaluating") 
             \/ /\ tsc.state = "QEvaluating"
                /\ SendMessage(msg.from, [type |-> "HASHES", 
                                          from |-> TSCs.pk, 
                                          task |-> tsc.address, 
                                        hashes |-> tsc.hashes])
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                  !.tasks = updatedTasks]
          /\ IF IsWorker(msg.from) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextUnique>>

(***************************************************************************)
(*                             RECV_SUBMIT_EVAL                            *)
(***************************************************************************)

ReceiveSubmitEval_TaskFormat(t, msg) ==
    /\ Cardinality(t.participants) = t.numParticipants
    /\ \/ /\ IsWorker(msg.from)
          /\ Workers[GetWorker(msg.from)].pk \in t.participants
          /\ t.requesterWeights # NULL
       \/ /\ IsRequester(msg.from)
          /\ msg.from = t.owner
          /\ t.requesterWeights = NULL

ReceiveSubmitEval_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "task", "weights"} : f \in DOMAIN msg
    /\ msg.type = "SUBMIT_EVAL"
    /\ \E t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg) 

ReceiveSubmitEval_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ \E msg \in TSCs.msgs : /\ ReceiveSubmitEval_MessageFormat(msg)
    
SubmitEval(taskSet, msg, taskId, userType) == 
    LET newTaskSet == {[t EXCEPT 
        !.state = IF userType = "WORKER" /\ t.taskId = taskId
                  THEN IF Cardinality(t.workerWeights) + 1 = t.numParticipants
                       THEN "Completed" 
                       ELSE "QEvaluating" 
                  ELSE t.state,
        !.workerWeights = IF userType = "WORKER" /\ t.taskId = taskId
                          THEN t.workerWeights \union {msg.weights}
                          ELSE t.workerWeights, 
        !.requesterWeights = IF userType = "REQUESTER" /\ t.taskId = taskId
                             THEN msg.weights
                             ELSE t.requesterWeights] : t \in taskSet}
     IN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                             !.tasks = newTaskSet]
                                        
    
ReceiveSubmitEval ==
    /\ ReceiveSubmitEval_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitEval_MessageFormat(m)
           updatedTasks == GetUpdatedTasks
           tsc == CHOOSE t \in updatedTasks : ReceiveSubmitEval_TaskFormat(t, msg)
       IN /\ \/ /\ HandleStateMismatch(tsc, msg, "QEvaluating") 
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}, 
                                        !.tasks = updatedTasks]
             \/ /\ tsc.state = "QEvaluating"
                /\ \/ /\ IsRequester(msg.from)
                      /\ SubmitEval(updatedTasks, msg, tsc.taskId, "REQUESTER")
                      /\ SendMessage(msg.from, [type |-> "ACK", 
                                                from |-> TSCs.pk, 
                                                task |-> tsc.address])
                   \/ /\ IsWorker(msg.from) 
                      /\ SubmitEval(updatedTasks, msg, tsc.taskId, "WORKER")
                      /\ SendMessage(msg.from, [type |-> "ACK", 
                                                from |-> TSCs.pk, 
                                                task |-> tsc.address])
          /\ IF IsWorker(msg.from) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextUnique>>

GlobalTimeout == 
    /\ Time >= MaxTime
    /\ TSCs' = [TSCs EXCEPT !.state = "TERMINATED"]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>
    
Terminating == /\ TSCs.state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

Next == 
    \/ /\ Time < MaxTime
       /\ \/ ReceivePostTasks
          \/ ReceiveQueryTasks
          \/ ReceiveConfirmTask
          \/ ReceiveSubmitHash
          \/ ReceiveQueryHashes
          \/ ReceiveSubmitEval
          \/ CheckReputation
    \/ GlobalTimeout
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Sun Mar 03 08:58:04 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
