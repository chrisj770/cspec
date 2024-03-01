-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

CONSTANT TaskPostDeadline

TypeOK == TRUE

Init == 
    TSCs = [state |-> "WORKING",
             msgs |-> {},
               pk |-> [address |-> "TSC", type |-> "public_key"],
            tasks |-> {}]  
           
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
       IN IF Time < TaskPostDeadline 
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
    
ReceiveQueryTasks_SendTasks(msg) == 
    LET matchingTSCs == IF IsWorker(msg.from) THEN TSCs.tasks 
                        ELSE {t \in TSCs.tasks : t.owner = msg.owner} 
        tscData == IF IsWorker(msg.from) 
                   THEN {GetWorkerTSC(t) : t \in matchingTSCs}
                   ELSE matchingTSCs
        response == [type |-> "TASKS",  
                     from |-> TSCs.pk, 
                    tasks |-> tscData]
    IN /\ SendMessage(msg.from, response)
       /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]

ReceiveQueryTasks == 
    /\ ReceiveQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveQueryTasks_MessageFormat(m)
       IN /\ IF Time >= TaskPostDeadline
             THEN ReceiveQueryTasks_SendTasks(msg)
             ELSE /\ SendMessage(msg.from, [type |-> "INVALID", from |-> TSCs.pk])
                  /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
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
           tsc == CHOOSE t \in TSCs.tasks : msg.task = t.address
           response == [from |-> TSCs.pk, task |-> tsc.address]
       IN \/ /\ msg.from \in tsc.participants
             /\ SendMessage(msg.from, response @@ [type |-> "CONFIRM_SUCCESS"])
             /\ UNCHANGED <<TSCs, USCs>>
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
    /\ msg.type = "REPUTATION" \equiv \A f \in {"reputation", "user", "task"} : f \in DOMAIN msg
    
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
       IN \/ /\ HandleStateMismatch(tsc, msg, "Unavailable")
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Unavailable"
             /\ \/ /\ msg.hash \in tsc.hashes
                   /\ UNCHANGED <<TSCs>>
                \/ SubmitHash(tsc, msg)
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
           tsc == CHOOSE t \in TSCs.tasks : ReceiveQueryHashes_TaskFormat(t, msg)
       IN /\ \/ /\ HandleStateMismatch(tsc, msg, "QEvaluating") 
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
    
SubmitEval(msg, tsc, userType) == 
    \/ /\ userType = "WORKER" 
       /\ TSCs' = [TSCs EXCEPT 
                  !.msgs = TSCs.msgs \ {msg},
                  !.tasks = {IF t.taskId = tsc.taskId 
                             THEN [t EXCEPT !.state = IF Cardinality(t.workerWeights) + 1 = t.numParticipants
                                                      THEN "Completed"
                                                      ELSE "QEvaluating",
                                            !.workerWeights = t.workerWeights \union {msg.weights}]
                             ELSE t : t \in TSCs.tasks}]
    \/ /\ userType = "REQUESTER"
       /\ TSCs' = [TSCs EXCEPT 
                  !.msgs = TSCs.msgs \ {msg},
                  !.tasks = {IF t.taskId = tsc.taskId 
                             THEN [t EXCEPT !.requesterWeights = msg.weights]
                             ELSE t : t \in TSCs.tasks}]
    
ReceiveSubmitEval ==
    /\ ReceiveSubmitEval_IsEnabled
    /\ LET msg == CHOOSE m \in TSCs.msgs : ReceiveSubmitEval_MessageFormat(m)
           tsc == CHOOSE t \in TSCs.tasks : ReceiveSubmitEval_TaskFormat(t, msg)
       IN /\ \/ /\ HandleStateMismatch(tsc, msg, "QEvaluating") 
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             \/ /\ tsc.state = "QEvaluating"
                /\ \/ /\ IsRequester(msg.from)
                      /\ SubmitEval(msg, tsc, "REQUESTER")
                      /\ SendMessage(msg.from, [type |-> "ACK", 
                                                from |-> TSCs.pk, 
                                                task |-> tsc.address])
                   \/ /\ IsWorker(msg.from) 
                      /\ SubmitEval(msg, tsc, "WORKER")
                      /\ SendMessage(msg.from, [type |-> "ACK", 
                                                from |-> TSCs.pk, 
                                                task |-> tsc.address])
          /\ IF IsWorker(msg.from) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextUnique>>

Next == 
    \/ ReceivePostTasks
    \/ ReceiveQueryTasks
    \/ ReceiveConfirmTask
    \/ ReceiveSubmitHash
    \/ ReceiveQueryHashes
    \/ ReceiveSubmitEval
    \/ CheckReputation

=============================================================================
\* Modification History
\* Last modified Fri Mar 01 11:30:12 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
