-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

USC == INSTANCE USC

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
    /\ USC!IsRequester(msg.from)
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
              newTaskList == addedTasks \union 
                             {AddFields(nextTask, msg.from, nextTaskId, nextAddress)} 
          IN PostTasks(Tail(tasksToAdd), newTaskList, msg) 

ReceivePostTasks == 
    /\ ReceivePostTasks_IsEnabled
    /\ \E msg \in TSCs.msgs : ReceivePostTasks_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceivePostTasks_MessageFormat(m) 
       IN /\ PostTasks(msg.tasks, {}, msg)
          /\ SendRequesterMessage(msg.from, [type |-> "ACK", from |-> TSCs.pk])                                  
    /\ UNCHANGED <<Workers, USCs>>

(***************************************************************************)
(*                             RECV_QUERY_TASKS                            *)
(***************************************************************************)
ReceiveQueryTasks_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "owner"} : f \in DOMAIN msg
    /\ msg.type = "QUERY_TASKS" 
    /\ IF USC!IsRequester(msg.from)
       THEN /\ msg.owner # NULL
       ELSE IF USC!IsWorker(msg.from) 
            THEN msg.owner = NULL
            ELSE FALSE 

ReceiveQueryTasks_IsEnabled == 
    /\ TSCs.state = "WORKING"
    /\ TSCs.TaskPostDeadline
    
ReceiveQueryTasks_SendTasks(tasks, msg) == 
    LET matchingTSCs == IF USC!IsWorker(msg.from) THEN tasks 
                        ELSE {t \in tasks : t.owner = msg.owner} 
        tscData == IF USC!IsWorker(msg.from) 
                   THEN {GetWorkerTSC(t) : t \in matchingTSCs}
                   ELSE matchingTSCs
        response == [type |-> "TASKS",  
                     from |-> TSCs.pk, 
                    tasks |-> tscData]
    IN \/ SendWorkerMessage(msg.from, response)
       \/ SendRequesterMessage(msg.from, response)

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ \E msg \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
       IN /\ \/ /\ USC!IsRequester(msg.from)
                /\ \A t \in TSCs.tasks : t.owner = msg.from => t.state = "Unavailable"  
                /\ ReceiveQueryTasks_SendTasks(TSCs.tasks, msg)
                /\ UNCHANGED <<Workers>>
             \/ /\ USC!IsWorker(msg.from)
                /\ ReceiveQueryTasks_SendTasks(TSCs.tasks, msg)
                /\ UNCHANGED <<Requesters>>
          /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<USCs, NextUnique>>           

(***************************************************************************)
(*                            RECV_CONFIRM_TASK                            *)
(***************************************************************************)
CanParticipate(reputation, task) == 
    /\ task.state \notin {"Canceled", "Completed"}
    /\ Cardinality(task.participants) < task.numParticipants
    /\ task.checkQ[reputation]
    
AddParticipant(taskSet, msg, taskId) == 
    LET newTaskList == {[t EXCEPT 
        !.participants = IF t.taskId = taskId 
                         THEN t.participants \union {msg.from} 
                         ELSE t.participants,
        !.state = IF t.taskId = taskId
                  THEN IF Cardinality(t.participants) + 1 = t.numParticipants
                       THEN "Unavailable"
                       ELSE "Available"
                  ELSE t.state] : t \in taskSet}
    IN TSCs' = [TSCs EXCEPT !.state = "WORKING",
                            !.msgs = TSCs.msgs \ {msg},
                            !.tasks = newTaskList]
                            
ReceiveConfirmTask_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ USC!IsWorker(msg.from)
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
             /\ SendWorkerMessage(msg.from, response @@ [type |-> "CONFIRM_SUCCESS"])
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ ~(msg.from \in tsc.participants)
             /\ \/ /\ tsc.state \in {"Unavailable", "QEvaluating"}
                   /\ SendWorkerMessage(msg.from, response @@ [type |-> "CONFIRM_FAIL"])
                \/ /\ tsc.state = "Canceled"
                   /\ SendWorkerMessage(msg.from, response @@ [type |-> "CANCELED"])
                \/ /\ tsc.state = "Completed"
                   /\ SendWorkerMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ ~(msg.from \in tsc.participants)
             /\ tsc.state = "Available"
             /\ LET reputation == USC!GetReputation(msg.from) 
                IN IF CanParticipate(reputation, tsc)
                   THEN /\ SendWorkerMessage(msg.from, [type |-> "CONFIRM_SUCCESS"] @@ response)
                        /\ AddParticipant(TSCs.tasks, msg, tsc.taskId)
                   ELSE /\ SendWorkerMessage(msg.from, [type |-> "CONFIRM_FAIL"] @@ response)
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
             /\ SendWorkerMessage(msg.from, response @@ [type |-> "ACK"])
          \/ /\ tsc.state = "Canceled"
             /\ SendWorkerMessage(msg.from, response @@ [type |-> "CANCELED"])
             /\ UNCHANGED <<TSCs>>
          \/ /\ tsc.state = "Completed"
             /\ SendWorkerMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ UNCHANGED <<TSCs>>              
    /\ UNCHANGED <<Requesters, USCs, NextUnique>>

(***************************************************************************)
(*                            RECV_QUERY_HASHES                            *)
(***************************************************************************)
ReceiveQueryHashes_TaskFormat(t, msg) == 
    /\ msg.from = t.owner

ReceiveQueryHashes_MessageFormat(msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ USC!IsRequester(msg.from)
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
             /\ SendRequesterMessage(msg.from, response @@ [type |-> "HASHES", hashes |-> tsc.hashes])
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Canceled"
             /\ SendRequesterMessage(msg.from, response @@ [type |-> "CANCELED"])
             /\ UNCHANGED <<TSCs>>
          \/ /\ tsc.state = "Completed"
             /\ SendRequesterMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ UNCHANGED <<TSCs>>
    /\ UNCHANGED <<Workers, USCs, NextUnique>>

(***************************************************************************)
(*                             RECV_SUBMIT_EVAL                            *)
(***************************************************************************)
ReceiveSubmitEval_TaskFormat(t, msg) ==
    /\ Cardinality(t.participants) = t.numParticipants
    /\ \/ /\ USC!IsWorker(msg.from)
          /\ Workers[GetWorker(msg.from)].pk \in t.participants
          /\ t.requesterWeights # NULL
       \/ /\ USC!IsRequester(msg.from)
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
                /\ \/ /\ USC!IsRequester(msg.from)
                      /\ SubmitEval(TSCs.tasks, msg, tsc.taskId, "REQUESTER")
                      /\ SendRequesterMessage(msg.from, response @@ [type |-> "ACK"])
                   \/ /\ USC!IsWorker(msg.from) 
                      /\ SubmitEval(TSCs.tasks, msg, tsc.taskId, "WORKER")
                      /\ SendWorkerMessage(msg.from, response @@ [type |-> "ACK"])
             \/ /\ tsc.state = "Canceled"
                /\ \/ SendWorkerMessage(msg.from, response @@ [type |-> "CANCELED"])
                   \/ SendRequesterMessage(msg.from, response @@ [type |-> "CANCELED"])
                /\ UNCHANGED <<TSCs>>
             \/ /\ tsc.state = "Completed"
                /\ \/ SendWorkerMessage(msg.from, response @@ [type |-> "COMPLETED"])
                   \/ SendRequesterMessage(msg.from, response @@ [type |-> "COMPLETED"])                
                /\ UNCHANGED <<TSCs>>                                    
          /\ IF USC!IsWorker(msg.from) 
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
    \/ /\ \E t \in TSCs.tasks : TaskExpired(t)
       /\ UpdateTasks
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Sun Mar 03 21:19:21 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
