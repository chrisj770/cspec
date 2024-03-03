-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

TypeOK == TRUE

Init == TSCs = [state |-> "WORKING",
                 msgs |-> {},
                   pk |-> [address |-> "TSC", type |-> "public_key"],
                tasks |-> {},
     TaskPostDeadline |-> FALSE]  

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
                         
TaskExpired(t) == 
    \/ /\ t.Sd
       /\ t.state \in {"Pending", "Available", "Unavailable"}
    \/ /\ t.Pd
       /\ t.state \in {"Pending", "Available", "Unavailable", "QEvaluating"} 
    
UpdateTasks == 
    /\ TSCs' = [TSCs EXCEPT !.tasks = {[t EXCEPT !.state = 
                    IF TaskExpired(t) THEN "Canceled" ELSE t.state] 
                    : t \in TSCs.tasks}]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>

(***************************************************************************)
(*                             RECV_POST_TASKS                             *)
(***************************************************************************)                 
ReceivePostTasks_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "tasks"} : f \in DOMAIN msg
    /\ IsRequester(msg.from)
    /\ msg.type = "POST_TASKS"

ReceivePostTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ ~TSCs.TaskPostDeadline
    
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
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN /\ PostTasks(msg.tasks, {}, msg)
          /\ SendMessage(msg.from, [type |-> "ACK", from |-> TSCs.pk])                                  
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
    /\ TSCs.TaskPostDeadline
    
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
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
       IN /\ \/ /\ IsRequester(msg.from)
                /\ \A t \in TSCs.tasks : t.owner = msg.from => t.state = "Unavailable"  
                /\ ReceiveQueryTasks_SendTasks(TSCs.tasks, msg)
                /\ UNCHANGED <<Workers>>
             \/ /\ IsWorker(msg.from)
                /\ ReceiveQueryTasks_SendTasks(TSCs.tasks, msg)
                /\ UNCHANGED <<Requesters>>
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
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
    /\ TSCs.TaskPostDeadline
                
ReceiveConfirmTask == 
    /\ ReceiveConfirmTask_IsEnabled
    /\ \E msg \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveConfirmTask_MessageFormat(m) 
           tsc == CHOOSE t \in TSCs.tasks : msg.task = t.address
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN \/ /\ msg.from \in tsc.participants
             /\ SendMessage(msg.from, response @@ [type |-> "CONFIRM_SUCCESS"])
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             /\ UNCHANGED <<USCs>>
          \/ /\ ~(msg.from \in tsc.participants)
             /\ \/ /\ tsc.state \in {"Unavailable", "QEvaluating"}
                   /\ SendMessage(msg.from, response @@ [type |-> "CONFIRM_FAIL"])
                \/ /\ tsc.state = "Canceled"
                   /\ SendMessage(msg.from, response @@ [type |-> "CANCELED"])
                \/ /\ tsc.state = "Completed"
                   /\ SendMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             /\ UNCHANGED <<USCs>>
          \/ /\ ~(msg.from \in tsc.participants)
             /\ tsc.state = "Available"
             /\ LET request == [type |-> "GET_REPUTATION", 
                                from |-> TSCs.pk, 
                                user |-> msg.from, 
                                task |-> msg.task]
                IN /\ SendMessage(USCs.pk, request) 
                   /\ TSCs' = [TSCs EXCEPT !.state = "CHECK_REPUTATION", 
                                           !.msgs = TSCs.msgs \ {msg}]
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
    /\ TSCs.TaskPostDeadline

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
    /\ \E msg \in TSCs.msgs : CheckReputation_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : CheckReputation_MessageFormat(m) 
           tsc == CHOOSE t \in TSCs.tasks : t.address = msg.task
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN IF msg.type = "REPUTATION"
          THEN IF CanParticipate(msg.reputation, tsc)  
               THEN /\ SendMessage(msg.user, [type |-> "CONFIRM_SUCCESS"] @@ response)
                    /\ AddParticipant(TSCs.tasks, msg, tsc.taskId)
               ELSE /\ SendMessage(msg.user, [type |-> "CONFIRM_FAIL"] @@ response)
                    /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                            !.state = "WORKING"]
          ELSE /\ SendMessage(msg.user, [type |-> "NOT_REGISTERED"] @@ response)
               /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg},
                                       !.state = "WORKING"]
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
    /\ TSCs.TaskPostDeadline

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
    /\ \E msg \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitHash_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveSubmitHash_TaskFormat(t, msg)
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN \/ /\ tsc.state = "Unavailable"
             /\ \/ /\ msg.hash \in tsc.hashes
                   /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
                \/ SubmitHash(TSCs.tasks, msg, tsc.taskId)
             /\ SendMessage(msg.from, response @@ [type |-> "ACK"])
          \/ /\ tsc.state = "Canceled"
             /\ SendMessage(msg.from, response @@ [type |-> "CANCELED"])
             /\ UNCHANGED <<TSCs>>
          \/ /\ tsc.state = "Completed"
             /\ SendMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ UNCHANGED <<TSCs>>              
    /\ UNCHANGED <<Requesters, USCs, NextUnique>>

(***************************************************************************)
(*                            RECV_QUERY_HASHES                            *)
(***************************************************************************)
ReceiveQueryHashes_TaskFormat(t, msg) == 
    /\ msg.from = t.owner

ReceiveQueryHashes_MessageFormat(msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ IsRequester(msg.from)
    /\ msg.type = "QUERY_HASHES"
    /\ \E t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)

ReceiveQueryHashes_IsEnabled ==
    /\ TSCs.state = "WORKING" 
    
ReceiveQueryHashes == 
    /\ ReceiveQueryHashes_IsEnabled
    /\ \E msg \in TSCs.msgs : ReceiveQueryHashes_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryHashes_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN \/ /\ tsc.state = "QEvaluating"
             /\ Cardinality(tsc.hashes) = tsc.numParticipants
             /\ SendMessage(msg.from, response @@ [type |-> "HASHES", hashes |-> tsc.hashes])
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Canceled"
             /\ SendMessage(msg.from, response @@ [type |-> "CANCELED"])
             /\ UNCHANGED <<TSCs>>
          \/ /\ tsc.state = "Completed"
             /\ SendMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ UNCHANGED <<TSCs>>
    /\ UNCHANGED <<Workers, USCs, NextUnique>>

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

ReceiveSubmitEval_IsEnabled == 
    /\ TSCs.state = "WORKING"
    
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
    /\ \E msg \in TSCs.msgs : /\ ReceiveSubmitEval_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitEval_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveSubmitEval_TaskFormat(t, msg)
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN /\ \/ /\ tsc.state = "QEvaluating"
                /\ \/ /\ IsRequester(msg.from)
                      /\ SubmitEval(TSCs.tasks, msg, tsc.taskId, "REQUESTER")
                      /\ SendMessage(msg.from, response @@ [type |-> "ACK"])
                   \/ /\ IsWorker(msg.from) 
                      /\ SubmitEval(TSCs.tasks, msg, tsc.taskId, "WORKER")
                      /\ SendMessage(msg.from, response @@ [type |-> "ACK"])
             \/ /\ tsc.state = "Canceled"
                /\ SendMessage(msg.from, response @@ [type |-> "CANCELED"])
                /\ UNCHANGED <<TSCs>>
             \/ /\ tsc.state = "Completed"
                /\ SendMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
                /\ UNCHANGED <<TSCs>>                                    
          /\ IF IsWorker(msg.from) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextUnique>>
    
Terminating == /\ TSCs.state = "WORKING"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

Next == 
    \/ /\ \A t \in TSCs.tasks : ~TaskExpired(t)
       /\ \/ ReceivePostTasks
          \/ ReceiveQueryTasks
          \/ ReceiveConfirmTask
          \/ ReceiveSubmitHash
          \/ ReceiveQueryHashes
          \/ ReceiveSubmitEval
          \/ CheckReputation
    \/ /\ \E t \in TSCs.tasks : TaskExpired(t)
       /\ UpdateTasks
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Sun Mar 03 16:11:21 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
