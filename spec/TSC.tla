-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC, Common 

USC == INSTANCE USC

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init == TSCs = [state |-> "WORKING",
                 msgs |-> {},
                   pk |-> [address |-> "TSC", type |-> "public_key"],
                tasks |-> {},
     TaskPostDeadline |-> FALSE]  

(***************************************************************************)
(* AddFields: This operator is invoked upon adding a Requester task, for   *)
(* which several default fields are added prior to being persisted by TSC. *)
(***************************************************************************) 
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

(***************************************************************************)
(* GetWorkerTask: This operator is invoked upon sending a list of tasks to *) 
(* a registered Worker, for which each task is reformatted to contain ONLY *)
(* information relevant to the Worker.                                     *)
(***************************************************************************)     
GetWorkerTask(t) == [Sd |-> t.Sd, 
                     Pd |-> t.Pd, 
                     Td |-> t.Td, 
                address |-> t.address, 
                 taskId |-> t.taskId, 
                  owner |-> t.owner, 
        numParticipants |-> t.numParticipants, 
               category |-> t.category,
                  state |-> t.state] 

(***************************************************************************)
(* UpdateTasks: This operator is invoked under the following conditions:   *)
(*                                                                         *) 
(*  - Any posted task reaches the Submission Deadline (Sd), but the task   *) 
(*     has failed to progress past the "Unavailable" state (i.e.           *) 
(*     confirmation or submission not complete)                            *)
(*                                                                         *)
(*  - Any posted task reaches the Proving Deadling (Pd), but the task      *)
(*     has failed to progress past the "QEvaluating" state (i.e.           *)
(*     evaluation by Workers/Requesters not complete)                      *)
(*                                                                         *) 
(* In either circumstance, the corresponding task is automatically updated *)
(* to state="Canceled" to prevent further processing.                      *)
(***************************************************************************)        
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
(*                                                                         *)
(* Receive "POST_TASKS" message from Requester containing a list of tasks  *) 
(* to be posted. Upon receipt, add each entry to the TSC's list of tasks   *) 
(* via the "PostTasks()" operator (which assigns unique "taskId"), then    *)
(* send "ACK" message to Requester.                                        *)
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
(*                                                                         *)
(* Receive "QUERY_TASKS" message from Worker/Requester requesting a list   *) 
(* of posted tasks. Upon receipt, perform an action based on the following *)
(* conditions:                                                             *)
(*                                                                         *)
(*  - If the message was sent by a Worker, send "TASKS" message to         *)
(*     Worker containing a list of all posted tasks (formatted via         *)
(*     "GetWorkerTask()" to remove unnecessary information).               *)
(*                                                                         *)
(*  - If the message was sent by a Requester and all tasks for which       *)
(*     the Requester is registered as an "owner" have state="Unavailable", *)
(*     send "TASKS" message to Requester containing a list of all          *) 
(*     relevant tasks.                                                     *)
(*                                                                         *)
(*  - Otherwise, ignore the message until either of the above conditions   *)
(*     are fulfilled. (NOTE: This prevents Requesters from repeatedly      *)
(*     sending "QUERY_TASKS" requests, which greatly expands state-space.) *)
(*                                                                         *)
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
                   THEN {GetWorkerTask(t) : t \in matchingTSCs}
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
(*                                                                         *)
(* Receive "CONFIRM_TASK" message from Worker requesting to register as a  *)
(* participant for any active task. Upon receipt, perform an action based  *) 
(* on the following conditions:                                            *)
(*                                                                         *)
(*  - If the Worker is already a participant for the specified task,       *) 
(*     send "CONFIRM_SUCCESS" message to Worker. Otherwise...              *)
(*                                                                         *)
(*  - If the specified task has state "Available" and the Worker does      *) 
(*     NOT qualify to participate via the "checkQ" function, send          *)
(*     "CONFIRM_FAIL" to Worker.                                           *)
(*                                                                         *)
(*  - If the specified task has state "Available" and the Worker           *)
(*     qualifies to participate via the "checkQ" function, add the Worker  *)
(*     to the task's list of participants and send "CONFIRM_SUCCESS"       *)
(*     to the Worker. (If the required number of participants is           *)
(*     reached, update the task state to "Unavailable".)                   *)
(*                                                                         *)
(*  - If the specified task has state "Unavailable" or "QEvaluating",      *)
(*     send "CONFIRM_FAIL" message to Worker.                              *) 
(*                                                                         *) 
(*  - If the specified task has state "Canceled" or "Completed",           *)
(*     send "CANCELED" or "COMPLETED" message to Worker, respectively.     *)
(*                                                                         *)
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
(*                                                                         *) 
(* Receive "SUBMIT_HASH" message from Worker containing a hash for         *)
(* encrypted sensory data. Upon receipt, perform an action based on the    *) 
(* following conditions:                                                   *)
(*                                                                         *)
(*  - If the specified task has state "Unavailable" and the Worker is      *)
(*    registered as a participant, add the hash to the task's "hashes"     *) 
(*    (if not already present) and send "ACK" message to Worker. (If       *)
(*    the required number of hashes is reached, update the task state      *) 
(*    to "QEvaluating".)                                                   *)
(*                                                                         *)
(*  - If the specified task has state "Canceled" or "Completed",           *)
(*     send "CANCELED" or "COMPLETED" message to Worker, respectively.     *)
(*                                                                         *)
(*  - Otherwise, ignore the message until either of the above conditions   *)
(*     are fulfilled. (NOTE: This allows out-of-sync workers to timeout    *) 
(*     and progress onto further tasks.)                                   *)
(*                                                                         *)
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
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Completed"
             /\ SendWorkerMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]            
    /\ UNCHANGED <<Requesters, USCs, NextUnique>>

(***************************************************************************)
(*                            RECV_QUERY_HASHES                            *)
(*                                                                         *) 
(* Receive "QUERY_HASHES" message from Requester requesting submitted      *)
(* hashes for a given task. Upon receipt, perform an action based on the   *) 
(* following conditions:                                                   *)
(*                                                                         *)
(*  - If the specified task has state "QEvaluating" and the Requester is   *)
(*    registered as the "owner", send "HASHES" message to Requester        *)
(*    containing the list of submitted hashes.                             *)
(*                                                                         *)
(*  - If the specified task has state "Canceled" or "Completed",           *)
(*     send "CANCELED" or "COMPLETED" message to Requester, respectively.  *)
(*                                                                         *)
(*  - Otherwise, ignore the message until either of the above conditions   *)
(*     are fulfilled. (NOTE: This prevents Requesters from receiving       *)
(*     hash lists before all Workers have submitted.)                      *)
(*                                                                         *)
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
    /\ TSCs.TaskPostDeadline
    
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
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
          \/ /\ tsc.state = "Completed"
             /\ SendRequesterMessage(msg.from, response @@ [type |-> "COMPLETED"])                   
             /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, USCs, NextUnique>>

(***************************************************************************)
(*                             RECV_SUBMIT_EVAL                            *)
(*                                                                         *)
(* Receive "SUBMIT_EVAL" message from Worker/Requester containing CATD     *) 
(* evaluation results for a given task. Upon receipt, perform an action    *)
(* based on the following conditions:                                      *)
(*                                                                         *)
(*  - If the message was sent by a participating Worker and the task       *)
(*     state is "QEvaluating", store the evaluation results and send       *)
(*     "ACK" to Worker. (If the required number of results is reached,     *)
(*     set task state to "Completed".)                                     *)
(*                                                                         *)
(*  - If the message was sent by a Requester and the task state is         *)
(*     "QEvaluating", store the evaluation results and send "ACK" to       *)
(*     Requester.                                                          *)
(*                                                                         *)
(*  - If the specified task has state "Canceled" or "Completed",           *)
(*     send "CANCELED" or "COMPLETED" message to Worker/Requester,         *)
(*     respectively.                                                       *)
(*                                                                         *)
(*  - Otherwise, ignore the message until any of the above conditions      *)
(*     are fulfilled. (NOTE: This allows out-of-sync parties to timeout    *)
(*     and progress onto further tasks.)                                   *)
(*                                                                         *)
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
    /\ TSCs.TaskPostDeadline
    
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
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
             \/ /\ tsc.state = "Completed"
                /\ \/ SendWorkerMessage(msg.from, response @@ [type |-> "COMPLETED"])
                   \/ SendRequesterMessage(msg.from, response @@ [type |-> "COMPLETED"])                
                /\ TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]                                   
          /\ IF USC!IsWorker(msg.from) 
             THEN UNCHANGED <<Requesters>>
             ELSE UNCHANGED <<Workers>>
    /\ UNCHANGED <<USCs, NextUnique>>

(***************************************************************************)
(* Terminating: Allows the TSC to remain working indefinitely, required by *)
(* TLA+ for stuttering.                                                    *)
(***************************************************************************)     
Terminating == /\ TSCs.state = "WORKING"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

(***************************************************************************)
(*                            ACTION DEFINITIONS                           *)
(***************************************************************************)
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
\* Last modified Tue Mar 19 14:04:49 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
