------------------------------- MODULE Worker -------------------------------
EXTENDS FiniteSets, Sequences, Common, TLC, Integers

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init ==
    Workers = [w \in 1..NumWorkers |-> [
                  msgs |-> {},              \* Message queue 
                 state |-> "SEND_REGISTER", \* Current state
               address |-> "",              \* Address/Pseudonym
                    pk |-> NULL,            \* Public key (obtained from USC during registration)
                    sk |-> NULL,            \* Private key (obtained from USC during registration)
          pendingTasks |-> {},              \* List of pending tasks (obtained from TSC during "RECV_QUERY_TASKS")
        confirmedTasks |-> {},              \* List of confirmed tasks (obtained via "CONFIRM_SUCCESS")
      unconfirmedTasks |-> {},              \* List of unconfirmed tasks (obtained via "CONFIRM_FAIL")
    currentConfirmTask |-> NULL,
           currentTask |-> NULL,            \* Current task 
           requesterSk |-> NULL,            \* Partial private key-share (obtained from Requester during "RECV_SEND_KEY")
           currentHash |-> NULL,            \* Data hash (obtained via submitting data to STORAGE during "RECV_SUBMIT_DATA")
      requesterWeights |-> NULL,            \* Evaluated worker weights (obtained from Requester during "RECV_WEIGHTS")
      participantsSent |-> {},              \* Set of other workers for sending cyphertext
      participantsRcvd |-> {},              \* Set of other workers for receiving cyphertexts
         submittedData |-> {},              \* Set of data submitted by all workers (obtained from other workers during "VERIFY")
               weights |-> {},
     TaskQueryDeadline |-> FALSE]] 

(***************************************************************************)
(* CATDAlgorithm: This operator is invoked during a Worker's "VERIFY"      *)
(* stage to simulate evaluation of received data. (NOTE: An implementation *)
(* of an actual truth-discovery algorithm is not included, as this remains *)
(* out-of-scope for this specification.)                                   *)
(***************************************************************************) 
CATDAlgorithm(i) == 
    {[participant |-> w.address, weight |-> "placeholder"] :
     w \in Workers[i].submittedData}

(***************************************************************************)
(* Terminate: This operator is invoked under a variety of circumstances,   *)
(* upon which a Worker transitions to state "TERMINATED" and remains idle  *)
(* indefinitely until all processing ceases.                               *) 
(***************************************************************************)     
Terminate(i, msg) == 
    Workers' = [Workers EXCEPT
        ![i].msgs = IF msg # NULL 
                    THEN Workers[i].msgs \ {msg}
                    ELSE Workers[i].msgs, 
        ![i].state = "TERMINATED",
        ![i].currentTask = NULL, 
        ![i].requesterSk = NULL,
        ![i].currentHash = NULL, 
        ![i].requesterWeights = NULL, 
        ![i].participantsSent = {},
        ![i].participantsRcvd = {}, 
        ![i].submittedData = {}, 
        ![i].weights = {}]

(***************************************************************************)
(* NextTask: This operator is invoked when (1) a task is successfully      *)
(* completed via the "RECV_SUBMIT_EVAL" state, (2) a message timeout has   *)
(* occurred in any "RECV" state, or (3) a task timeout has occurred due to *)
(* the Submission/Proving deadline elapsing before all necessary Worker    *)
(* actions have been completed.                                            *)
(*                                                                         *)
(* If 1+ confirmed tasks remain, set "currentTask" to the next confirmed   *)
(* task (w/ lowest "taskId") and transition to state "RECV_SEND_KEY". If 0 *)
(* confirmed tasks remain, transition to "SEND_QUERY_TASKS" to re-query    *)
(* the TSC for additional tasks.                                           *) 
(***************************************************************************)
GetNextTask(i) == 
    IF Cardinality(Workers[i].confirmedTasks) = 0 THEN NULL 
    ELSE CHOOSE t \in Workers[i].confirmedTasks : \A y \in Workers[i].tasks : 
                t.taskId # y.taskId => t.taskId < y.taskId 

NextTask(i, msg) == 
    LET nextTask == GetNextTask(i)
    IN Workers' = [Workers EXCEPT 
        ![i].msgs = IF msg # NULL 
                    THEN Workers[i].msgs \ {msg}
                    ELSE Workers[i].msgs,
        ![i].state = IF nextTask = NULL 
                     THEN "SEND_QUERY_TASKS"
                     ELSE "RECV_SEND_KEY", 
        ![i].confirmedTasks = Workers[i].confirmedTasks \ {nextTask},
        ![i].currentTask = nextTask, 
        ![i].requesterSk = NULL,
        ![i].currentHash = NULL, 
        ![i].requesterWeights = NULL, 
        ![i].participantsSent = {},
        ![i].participantsRcvd = {}, 
        ![i].submittedData = {}, 
        ![i].weights = {}]
           
(***************************************************************************)
(*                             SEND_REGISTER                               *)
(*                                                                         *)
(* Send "REGISTER" message to USC to register as Worker, then transition   *)
(* immediately to "RECV_REGISTER" upon completion.                         *)
(***************************************************************************)
SendRegister_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_REGISTER"

SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                   userType |-> "WORKER", 
                       from |-> i]
       IN /\ SendUSCMessage(request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Requesters, TSCs, Storage>>
    
(***************************************************************************)
(*                             RECV_REGISTER                               *)
(*                                                                         *)
(* Await "REGISTERED" message from USC with address and private/public     *)
(* key-share, indicating that the Worker has been successfully registered. *)
(* Transition to "SEND_QUERY_TASKS" upon receipt of expected message, or   *)
(* terminate early upon timeout or receipt of "NOT_REGISTERED".            *)
(***************************************************************************)
ReceiveRegister_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = USCs.pk
    /\ msg.type \in {"REGISTERED", "NOT_REGISTERED"}
    /\ msg.type = "REGISTERED" \equiv \A f \in {"key", "pk", "sk"}: f \in DOMAIN msg

ReceiveRegister_IsEnabled(i) ==
    /\ Workers[i].state = "RECV_REGISTER"

ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, msg)    
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, m)
       IN \/ /\ msg.type = "REGISTERED" 
             /\ Workers' = [Workers EXCEPT ![i].address = msg.key,
                                           ![i].pk = msg.pk,
                                           ![i].sk = msg.sk,
                                           ![i].msgs = Workers[i].msgs \ {msg}, 
                                           ![i].state = "SEND_QUERY_TASKS"]
          \/ /\ msg.type # "REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveRegister_Timeout(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ ~(\E msg \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, msg))
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
        
(***************************************************************************)
(*                            SEND_QUERY_TASKS                             *)
(*                                                                         *)
(* Send "QUERY_TASKS" message to TSC to retrive list of posted tasks, then *)
(* transition immediately to "RECV_QUERY_TASKS" upon completion.           *)
(***************************************************************************)
SendQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_QUERY_TASKS"

SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                       from |-> Workers[i].pk,
                      owner |-> NULL]
       IN /\ SendTSCMessage(request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>
    
(***************************************************************************)
(*                            RECV_QUERY_TASKS                             *)
(*                                                                         *)
(* Await "TASKS" message from TSC containing a list of posted tasks. Upon  *)
(* receiving the expected message, select a subset with state="Available"  *)
(* to accept and store relevant information before transitioning to        *)
(* "SEND_CONFIRM_TASK". Otherwise, terminate early upon (1) timeout, (2)   *)
(* receipt of an empty task list, or (3) receipt of a non-empty task list  *)
(* containing 0 tasks with state="Available".                              *)
(***************************************************************************)    
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"TASKS", "NOT_REGISTERED"}
    /\ msg.type = "TASKS" \equiv "tasks" \in DOMAIN msg

ReceiveQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_QUERY_TASKS"
    
ReceiveQueryTasks_Success(i, msg) == 
    LET validTasks == {t \in msg.tasks : 
            /\ t.state = "Available"
            /\ t.taskId \notin {s.taskId : s \in Workers[i].unconfirmedTasks}
            /\ t.taskId \notin {s.taskId : s \in Workers[i].confirmedTasks}}
    IN IF Cardinality(validTasks) = 0 
       THEN Terminate(i, msg)
       ELSE Workers' = [Workers EXCEPT 
                    ![i].msgs = Workers[i].msgs \ {msg},
                    ![i].pendingTasks = validTasks,
                    ![i].state = "SEND_CONFIRM_TASK"]
    
ReceiveQueryTasks(i) ==
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, msg)    
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, m)
       IN \/ /\ msg.type = "TASKS" 
             /\ ReceiveQueryTasks_Success(i, msg)
          \/ /\ msg.type # "TASKS"
             /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                           ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveQueryTasks_Timeout(i) == 
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ ~(\E msg \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, msg))
    /\ Terminate(i, NULL) 
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                           SEND_CONFIRM_TASK                             *)
(*                                                                         *)
(* For the next pending task, send "CONFIRM_TASK" message with relevant    *)
(* task information to TSC to register as a participant, then transition   *)
(* immediately to "RECV_CONFIRM_TASK" upon completion.                     *) 
(***************************************************************************)
SendConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_CONFIRM_TASK" 
    /\ \E t \in Workers[i].pendingTasks : /\ t \notin Workers[i].unconfirmedTasks
                                          /\ t \notin Workers[i].confirmedTasks

SendConfirmTask(i) == 
    /\ SendConfirmTask_IsEnabled(i)
    /\ LET nextConfTask == CHOOSE tsc \in Workers[i].pendingTasks :
                           /\ \A other \in Workers[i].pendingTasks: 
                               tsc # other => tsc.taskId < other.taskId
                           /\ tsc \notin Workers[i].unconfirmedTasks
                           /\ tsc \notin Workers[i].confirmedTasks
           request == [type |-> "CONFIRM_TASK", 
                       from |-> Workers[i].pk, 
                       task |-> nextConfTask.address]
       IN /\ SendTSCMessage(request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_CONFIRM_TASK",
                                        ![i].currentConfirmTask = nextConfTask]
    /\ UNCHANGED <<Requesters, USCs, Storage>>
    
(***************************************************************************)
(*                           RECV_CONFIRM_TASK                             *)
(*                                                                         *)
(* Await any message from TSC indicating the state of confirmation. If the *)
(* message is "CONFIRM_SUCCESS", move the current pending task to the      *)
(* "confirmedTasks" list for later processing. Otherwise, move it to the   *)
(* "unconfirmedTasks" list to prevent re-registration in future queries.   *) 
(* Finally, perform a state transition based on the following conditions:  *)
(*                                                                         *)
(*  - If 1+ pending tasks remain, transition to "SEND_CONFIRM_TASK".       *)
(*                                                                         *)
(*  - If 0 pending tasks remain and 0 tasks have been successfully         *)
(*     confirmed (i.e. "confirmedTasks" is empty), transition to           *)
(*     "SEND_QUERY_TASKS" to re-query the TSC.                             *)
(*                                                                         *)
(*  - If 0 pending tasks remain and 1+ tasks have been successfully        *)
(*     confirmed, set the "currentTask" as the confirmed task with         *)
(*     the lowest "taskId" and transition to "RECV_SEND_KEY".              *)
(*                                                                         *)
(* Alternatively, should a timeout occur, move the current pending task to *)
(* "unconfirmedTasks" and perform a state transition as described above.   *) 
(***************************************************************************)
ReceiveConfirmTask_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"CANCELED", "COMPLETED", "CONFIRM_FAIL", "CONFIRM_SUCCESS", "NOT_REGISTERED"}
    /\ msg.type \in {"CANCELED", "COMPLETED", "CONFIRM_FAIL", "CONFIRM_SUCCESS"} => 
        /\ "task" \in DOMAIN msg
        /\ msg.task = Workers[i].currentConfirmTask.address

ReceiveConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_CONFIRM_TASK"
    
ReceiveConfirmTask_Success(i, msg, task) == 
    LET finished == Cardinality(Workers[i].pendingTasks) = 1 
        newTasks == Workers[i].confirmedTasks \union {task} 
        firstTask == CHOOSE t \in newTasks: \A y \in newTasks: 
                            t.taskId # y.taskId => t.taskId < y.taskId
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].pendingTasks = {t \in Workers[i].pendingTasks : t.taskId # task.taskId}, 
                   ![i].confirmedTasks = IF finished THEN newTasks \ {firstTask} ELSE newTasks,
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN "RECV_SEND_KEY" ELSE "SEND_CONFIRM_TASK", 
                   ![i].currentConfirmTask = NULL]

ReceiveConfirmTask_Failed(i, msg, task) == 
    LET finished == Cardinality(Workers[i].pendingTasks) = 1 
        firstTask == IF Cardinality(Workers[i].confirmedTasks) = 0 THEN NULL 
                     ELSE CHOOSE t \in Workers[i].confirmedTasks: \A y \in Workers[i].confirmedTasks: 
                                 t.taskId # y.taskId => t.taskId < y.taskId
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].pendingTasks = {t \in Workers[i].pendingTasks : t.taskId # task.taskId},
                   ![i].confirmedTasks = IF finished THEN 
                                            IF Cardinality(Workers[i].confirmedTasks) > 0
                                            THEN Workers[i].confirmedTasks \ {firstTask}
                                            ELSE {} 
                                         ELSE Workers[i].confirmedTasks,    
                   ![i].unconfirmedTasks = Workers[i].unconfirmedTasks \union {task},          
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN
                                    IF Cardinality(Workers[i].confirmedTasks) > 0
                                    THEN "RECV_SEND_KEY"
                                    ELSE "SEND_QUERY_TASKS"
                                ELSE "SEND_CONFIRM_TASK",
                   ![i].currentConfirmTask = NULL]
                                
ReceiveConfirmTask(i) == 
    /\ ReceiveConfirmTask_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, msg)    
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, m)
       IN \/ /\ msg.type # "NOT_REGISTERED"
             /\ \/ /\ msg.type = "CONFIRM_SUCCESS" 
                   /\ ReceiveConfirmTask_Success(i, msg, Workers[i].currentConfirmTask)
                \/ /\ msg.type # "CONFIRM_SUCCESS"
                   /\ ReceiveConfirmTask_Failed(i, msg, Workers[i].currentConfirmTask)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveConfirmTask_Timeout(i) == 
    /\ ReceiveConfirmTask_IsEnabled(i)
    /\ ~(\E msg \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, msg))
    /\ ReceiveConfirmTask_Failed(i, NULL, Workers[i].currentConfirmTask)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                             RECV_SEND_KEY                               *)
(*                                                                         *)
(* Await "SEND_KEY" message from Requester containing a private key-share  *)
(* encrypted via the Worker's public key. Upon receipt, decrypt the key-   *)
(* share via the Worker's private key, then send an "ACK" message to the   *)
(* Requester and transition immediately to "COMPUTE" upon completion.      *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or re-query TSC) via the logic defined in "NextTask".                  *)
(***************************************************************************)
ReceiveSendKey_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task", "keyshare"} : f \in DOMAIN msg
    /\ msg.from = Workers[i].currentTask.owner
    /\ msg.type = "SEND_KEY" 
    /\ msg.task = Workers[i].currentTask.address

ReceiveSendKey_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SEND_KEY"
    /\ Workers[i].requesterSk = NULL
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd

ReceiveSendKey(i) == 
    /\ ReceiveSendKey_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, msg)     
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, m)
           decryptedKeyshare == Decrypt(msg.keyshare, Workers[i].sk)
           response == [type |-> "ACK", 
                        from |-> Workers[i].pk,
                        task |-> Workers[i].currentTask.address]
       IN /\ SendRequesterMessage(msg.from, response)
          /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                        ![i].requesterSk = decryptedKeyshare, 
                                        ![i].state = "COMPUTE"] 
    /\ UNCHANGED <<TSCs, USCs, Storage>>
    
ReceiveSendKey_Timeout(i) == 
    /\ ReceiveSendKey_IsEnabled(i)
    /\ ~(\E msg \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>> 
    
(***************************************************************************)
(*                                 COMPUTE                                 *)
(*                                                                         *)
(* Generate sensory data and store locally, then transition immediately to *)
(* "SEND_SUBMIT_DATA" upon completion.                                     *)
(***************************************************************************)
Compute_IsEnabled(i) == 
    /\ Workers[i].state = "COMPUTE"
    /\ Workers[i].requesterSk # NULL 
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd
    
Compute(i) == 
    /\ Compute_IsEnabled(i) 
    /\ Workers' = [Workers EXCEPT ![i].state = "SEND_SUBMIT_DATA"] \* TODO
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                             SEND_SUBMIT_DATA                            *)
(*                                                                         *)
(* Encrypt generated sensory data via Requester's public key-share, send   *)
(* "SUBMIT_DATA" message containing encrypted data to Storage, then        *)
(* transition immediately to "RECV_SUBMIT_DATA" upon completion.           *)
(***************************************************************************)
SendSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_DATA" 
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd

SendSubmitData(i) == 
    /\ SendSubmitData_IsEnabled(i) 
    /\ LET encryptedData == Encrypt("DataPlaceholder", Workers[i].currentTask.owner @@ 
                                                       [share |-> Workers[i].requesterSk.share])
           request == [type |-> "SUBMIT_DATA", 
                       from |-> Workers[i].pk, 
                       data |-> encryptedData]
       IN /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {request}]
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_DATA"]
    /\ UNCHANGED <<Requesters, TSCs, USCs>>

(***************************************************************************)
(*                             RECV_SUBMIT_DATA                            *)
(*                                                                         *)
(* Await "HASH" message from Storage containing hash of encrypted data.    *)
(* Upon receipt, store the returned hash and transition immediately to     *)
(* "SEND_SUBMIT_HASH" upon completion.                                     *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or re-query TSC) via the logic defined in "NextTask".                  *)
(***************************************************************************)
ReceiveSubmitData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "hash"} : f \in DOMAIN msg
    /\ msg.type = "HASH" 
    /\ msg.from = Storage.pk

ReceiveSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_DATA" 
    /\ Workers[i].requesterSk # NULL 
    /\ Workers[i].currentHash = NULL
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd

ReceiveSubmitData(i) == 
    /\ ReceiveSubmitData_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitData_MessageFormat(i, msg)    
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitData_MessageFormat(i, m) 
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                     ![i].state = "SEND_SUBMIT_HASH",
                                     ![i].currentHash = msg.hash]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveSubmitData_Timeout(i) == 
    /\ ReceiveSubmitData_IsEnabled(i) 
    /\ ~(\E msg \in Workers[i].msgs : ReceiveSubmitData_MessageFormat(i, msg)) 
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                             SEND_SUBMIT_HASH                            *)
(*                                                                         *)
(* Send "SUBMIT_HASH" message to TSC containing the data hash previously   *)
(* received from Storage, then transition immediately to "RECV_SUBMIT_HASH"*)
(* upon completion.                                                        *)
(***************************************************************************)
SendSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_HASH"
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentHash # NULL
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd

SendSubmitHash(i) ==
    /\ SendSubmitHash_IsEnabled(i)
    /\ LET request == [type |-> "SUBMIT_HASH", 
                       from |-> Workers[i].pk,
                       hash |-> Workers[i].currentHash,
                       task |-> Workers[i].currentTask.address]
       IN /\ SendTSCMessage(request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_HASH"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>
    
(***************************************************************************)
(*                             RECV_SUBMIT_HASH                            *)
(*                                                                         *)
(* Await any message from TSC indicating receipt status of the data hash.  *)
(* If the message is "ACK", transition to "RECV_WEIGHTS". In all other     *) 
(* circumstances (including timeout), reset and transition to the next     *)
(* confirmed task (or re-query TSC) via the logic defined in "NextTask".   *)
(***************************************************************************)
ReceiveSubmitHash_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg 
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "COMPLETED", "CANCELED", "NOT_REGISTERED"}
    /\ msg.type \in {"ACK", "COMPLETED", "CANCELED"} => "task" \in DOMAIN msg

ReceiveSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_HASH" 
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Sd

ReceiveSubmitHash(i) == 
    /\ ReceiveSubmitHash_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, m)
       IN \/ /\ msg.type = "ACK"
             /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                           ![i].state = "RECV_WEIGHTS"]
          \/ /\ msg.type # "ACK"
             /\ NextTask(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveSubmitHash_Timeout(i) == 
    /\ ReceiveSubmitHash_IsEnabled(i) 
    /\ ~(\E msg \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                              RECV_WEIGHTS                               *)
(*                                                                         *)
(* Await "WEIGHTS" message from Requester containing evaluation results    *)
(* for each Worker. Upon receipt, store the results and the list of other  *)
(* participants locally (within "participantsSent" and "participantsRcvd") *)
(* for further processing. Then send an "ACK" message to the Requester and *)
(* transition to "SEND_QUERY_DATA".                                        *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or re-query TSC) via the logic defined in "NextTask".                  *)
(***************************************************************************)
ReceiveWeights_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task", "weights"} : f \in DOMAIN msg
    /\ msg.from = Workers[i].currentTask.owner
    /\ msg.task = Workers[i].currentTask.address 
    /\ msg.type = "WEIGHTS"

ReceiveWeights_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_WEIGHTS"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].requesterSk # NULL
    /\ ~Workers[i].currentTask.Pd
    
ReceiveWeights(i) == 
    /\ ReceiveWeights_IsEnabled(i) 
    /\ \E msg \in Workers[i].msgs : ReceiveWeights_MessageFormat(i, msg) 
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveWeights_MessageFormat(i, m)
           otherParticipants == {w.address : w \in {weight \in msg.weights : 
                                 weight.address # Workers[i].pk}}
           response == [type |-> "ACK", 
                        from |-> Workers[i].pk,
                        task |-> Workers[i].currentTask.address] 
       IN /\ SendRequesterMessage(msg.from, response)
          /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg}, 
                                        ![i].requesterWeights = msg.weights,
                                        ![i].participantsSent = otherParticipants, 
                                        ![i].participantsRcvd = otherParticipants,
                                        ![i].state = "SEND_QUERY_DATA"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>
    
ReceiveWeights_Timeout(i) == 
    /\ ReceiveWeights_IsEnabled(i) 
    /\ ~(\E msg \in Workers[i].msgs : ReceiveWeights_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                             SEND_QUERY_DATA                             *)
(*                                                                         *)
(* Send "QUERY_DATA" message to Storage to request submitted data for the  *)
(* Worker's stored hash, then transition immediately to "RECV_QUERY_DATA"  *)
(* upon completion.                                                        *)
(***************************************************************************)
SendQueryData_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_QUERY_DATA"
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Pd

SendQueryData(i) == 
    /\ SendQueryData_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_DATA", 
                       from |-> Workers[i].pk, 
                     hashes |-> {Workers[i].currentHash}]
       IN /\ SendStorageMessage(request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Requesters, TSCs, USCs>> 

(***************************************************************************)
(*                             RECV_QUERY_DATA                             *)
(*                                                                         *)
(* Await "DATA" message from Storage containing encrypted sensory data     *)
(* corresponding to the Worker's stored hash. Upon receipt, decrypt the    *)
(* data via the Requester's private key-share and store for later          *)
(* processing. Then, either (1) transition to "VERIFY" if the list of      *)
(* other participants ("participantsSent") is empty, or (2) transition to  *)
(* "REQUEST_DATA" if the list contains 1+ participant(s).                  *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or re-query TSC) via the logic defined in "NextTask".                  *)
(***************************************************************************)    
ReceiveQueryData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "allData"} : f \in DOMAIN msg
    /\ msg.from = Storage.pk
    /\ msg.type = "DATA"

ReceiveQueryData_IsEnabled(i) ==
    /\ Workers[i].state = "RECV_QUERY_DATA"
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Pd

ReceiveQueryData(i) == 
    /\ ReceiveQueryData_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveQueryData_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveQueryData_MessageFormat(i, m)
           decryptedData == {[address |-> d.address,
                              submission |-> Decrypt(d.submission, Workers[i].requesterSk)]
                            : d \in msg.allData}
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                     ![i].submittedData = decryptedData,
                                     ![i].state = IF Cardinality(Workers[i].participantsSent) > 0 
                                                  THEN "REQUEST_DATA"
                                                  ELSE "VERIFY"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveQueryData_Timeout(i) == 
    /\ ReceiveQueryData_IsEnabled(i) 
    /\ ~(\E msg \in Workers[i].msgs : ReceiveQueryData_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>    
    
(***************************************************************************)
(*                               REQUEST_DATA                              *)
(*                                                                         *)
(* For the next Worker in list of sent participants ("participantsSent"),  *)
(* send "GET_DATA" message to Worker to request decrypted sensory data,    *)
(* then transition immediately to "RECV_DATA" upon completion.             *)
(***************************************************************************)
RequestData_IsEnabled(i) == 
    /\ Workers[i].state = "REQUEST_DATA"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].submittedData # {}
    /\ Workers[i].participantsSent # {}
    /\ ~Workers[i].currentTask.Pd
    
RequestData(i) == 
    /\ RequestData_IsEnabled(i)
    /\ LET nextWorkerPk == CHOOSE r \in Workers[i].participantsSent : TRUE
           wIndex == CHOOSE index \in 1..NumWorkers : Workers[index].pk = nextWorkerPk
           request == [type |-> "GET_DATA",
                       from |-> Workers[i].pk,
                       task |-> Workers[i].currentTask.address]
       IN Workers' = [Workers EXCEPT ![i].state = "RECV_DATA", 
                                     ![wIndex].msgs = Workers[wIndex].msgs \union {request}]                  
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                                 RECV_DATA                               *)
(*                                                                         *)
(* Await "DATA" message from Worker containing decrypted sensory data.     *)
(* Upon receipt, store the data in "submittedData" for further processing  *)
(* and remove the corresponding Worker from "participantsSent" to prevent  *)
(* from repeating the same request. Then, perform a state transition based *)
(* on the following conditions:                                            *)
(*                                                                         *)
(*  - If 1+ un-queried Workers remain in "participantsSent", transition    *)
(*     to "REQUEST_DATA".                                                  *)
(*                                                                         *)
(*  - If 0 un-queried Workers remain in "participantsSent" and 1+ Workers  *)
(*     remain in "participantsRcvd" (i.e. sensory data has not been sent   *)
(*     to all workers), remain in state "RECV_DATA".                       *)       
(*                                                                         *)
(*  - If 0 un-queried Workers remain in "participantsSent" and 0 Workers   *)
(*     remain in "participantsRcvd", transition to "VERIFY".               *)
(*                                                                         *)
(* Alternatively, should a timeout occur, reset and transition to the next *)
(* confirmed task or (re-query TSC) via the logic defined in "NextTask".   *)
(***************************************************************************)
ReceiveData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task", "data"} : f \in DOMAIN msg
    /\ msg.from \in Workers[i].participantsSent
    /\ msg.type = "DATA"
    /\ msg.task = Workers[i].currentTask.address

ReceiveData_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_DATA"
    /\ Workers[i].currentTask # NULL 
    /\ ~Workers[i].currentTask.Pd

ReceiveData(i) == 
    /\ ReceiveData_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveData_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveData_MessageFormat(i, m) 
           worker == CHOOSE w \in Workers[i].participantsSent : w = msg.from
       IN Workers' = [Workers EXCEPT 
                ![i].msgs = Workers[i].msgs \ {msg}, 
                ![i].participantsSent = Workers[i].participantsSent \ {worker},
                ![i].submittedData = Workers[i].submittedData \union {msg.data}, 
                ![i].state = IF Cardinality(Workers[i].participantsSent) = 1 
                             THEN IF /\ Cardinality(Workers[i].participantsRcvd) = 0 
                                     /\ Cardinality(Workers[i].submittedData) + 1 = 
                                        Workers[i].currentTask.numParticipants 
                                  THEN "VERIFY"
                                  ELSE "RECV_DATA"
                             ELSE "REQUEST_DATA"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>  
    
ReceiveData_Timeout(i) == 
    /\ ReceiveData_IsEnabled(i) 
    /\ ~(\E msg \in Workers[i].msgs : ReceiveData_MessageFormat(i, msg))
    /\ NextTask(i, NULL) 
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

(***************************************************************************)
(* SendData: Receive "GET_DATA" message from another Worker while in       *)
(* "REQUEST_DATA" or "RECV_DATA" states. Upon receipt, send "DATA" message *)
(* to Worker containing decrypted sensory data, then remove the Worker     *) 
(* from the list of received participants ("participantsRcvd") to prevent  *)
(* from repeating the same response. Finally, perform a state transition   *)
(* based on the following conditions:                                      *)
(*                                                                         *)
(*  - If 0 un-queried Workers remain in "participantsSent" and 0 Workers   *)
(*     remain in "participantsRcvd" (as result of this action), transition *)
(*     to "VERIFY".                                                        *)
(*                                                                         *)
(*  - Otherwise, return to the previously-held state.                      *)
(*                                                                         *)
(* NOTE: This definition does NOT represent a Worker state, but rather an  *)
(* intermediary action to be taken between processing of "REQUEST_DATA" or *)
(* "RECV_DATA" states. Therefore, it only manages necessary state updates  *)
(* and does not handle timeouts during data exchange.                      *)
(***************************************************************************)    
SendData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from \in Workers[i].participantsRcvd
    /\ msg.type = "GET_DATA"
    /\ msg.task = Workers[i].currentTask.address
    
SendData_IsEnabled(i) == 
    /\ Workers[i].state \in {"REQUEST_DATA", "RECV_DATA"} 
    /\ Workers[i].currentTask # NULL 
    /\ \E msg \in Workers[i].msgs : SendData_MessageFormat(i, msg)
    /\ ~Workers[i].currentTask.Pd
    
SendData(i) == 
    /\ SendData_IsEnabled(i) 
    /\ LET msg == CHOOSE m \in Workers[i].msgs : SendData_MessageFormat(i, m) 
           worker == CHOOSE w \in Workers[i].participantsRcvd : w = msg.from
           wIndex == CHOOSE index \in 1..NumWorkers : Workers[index].pk = worker
           response == [type |-> "DATA", 
                        from |-> Workers[i].pk, 
                        data |-> CHOOSE w \in Workers[i].submittedData : 
                                 w.address = Workers[i].pk,
                        task |-> Workers[i].currentTask.address]
       IN /\ Workers' = [Workers EXCEPT 
                    ![i].msgs = Workers[i].msgs \ {msg}, 
                    ![i].participantsRcvd = Workers[i].participantsRcvd \ {worker}, 
                    ![i].state = IF /\ Cardinality(Workers[i].participantsRcvd) = 1
                                    /\ Cardinality(Workers[i].participantsSent) = 0
                                    /\ Cardinality(Workers[i].submittedData)= 
                                       Workers[i].currentTask.numParticipants
                                 THEN "VERIFY"
                                 ELSE Workers[i].state,
                    ![wIndex].msgs = Workers[wIndex].msgs \union {response}]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
       
(***************************************************************************)
(*                                  VERIFY                                 *)
(*                                                                         *)
(* Run CATD Algorithm on sensory data received from other Workers, then    *)
(* transition immediately to "SEND_SUBMIT_EVAL" upon completion.           *)
(***************************************************************************)
Verify_IsEnabled(i) == 
    /\ Workers[i].state = "VERIFY"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].requesterSk # NULL
    /\ ~Workers[i].currentTask.Pd

Verify(i) == 
    /\ Verify_IsEnabled(i)
    /\ LET weights == CATDAlgorithm(i)
       IN Workers' = [Workers EXCEPT ![i].weights = weights, 
                                     ![i].state = "SEND_SUBMIT_EVAL"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                            SEND_SUBMIT_EVAL                             *)
(*                                                                         *)
(* Send "SUBMIT_EVAL" message to TSC containing evaluation results, then   *)
(* transition immediately to "RECV_SUBMIT_EVAL" upon completion.           *)
(***************************************************************************)
SendSubmitEval_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_EVAL"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].weights # NULL
    /\ ~Workers[i].currentTask.Pd

SendSubmitEval(i) == 
    /\ SendSubmitEval_IsEnabled(i) 
    /\ LET request == [type |-> "SUBMIT_EVAL",
                       from |-> Workers[i].pk,
                       task |-> Workers[i].currentTask.address,
                    weights |-> Workers[i].weights]
       IN /\ SendTSCMessage(request) 
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_EVAL"]
    /\ UNCHANGED <<Requesters, USCs, Storage>> 

(***************************************************************************)
(*                            RECV_SUBMIT_EVAL                             *)
(*                                                                         *)
(* Await any message from TSC indicating receipt status of evaluation      *)
(* results. Upon receipt of any valid message (or timeout), reset and      *)
(* transition to the next confirmed task (or re-query TSC) via the logic   *)
(* defined in "NextTask".                                                  *)
(***************************************************************************)
ReceiveSubmitEval_MessageFormat(i, msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "CANCELED", "COMPLETED"}

ReceiveSubmitEval_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_EVAL" 
    /\ Workers[i].currentTask # NULL
    /\ ~Workers[i].currentTask.Pd 
    
ReceiveSubmitEval(i) ==
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitEval_MessageFormat(i, m)
       IN NextTask(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
ReceiveSubmitEval_Timeout(i) == 
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ ~(\E msg \in Workers[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg))
    /\ NextTask(i, NULL) 
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
        
(***************************************************************************)
(* EarlyTermination: This action is invoked when a Worker has failed to    *)
(* progress through the "RECV_QUERY_TASKS" state (i.e. receive a task list *)
(* and accept at least 1 task) before the "TaskQueryDeadline" elapses. In  *)
(* this case, the Worker terminates immediately w/o further processing.    *) 
(***************************************************************************)
EarlyTermination_IsEnabled(i) == 
    /\ Workers[i].TaskQueryDeadline
    /\ Workers[i].state \in {"INIT", 
                             "SEND_REGISTER", 
                             "RECV_REGISTER",
                             "SEND_QUERY_TASKS", 
                             "RECV_QUERY_TASKS"}
                             
EarlyTermination(i) == 
    /\ EarlyTermination_IsEnabled(i) 
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

(***************************************************************************)
(* TaskTimeout: This action is invoked under the following conditions:     *)
(*                                                                         *)
(*  - A Worker has accepted a task for which the Submission Deadline (Sd)  *) 
(*     has elapsed, but the Worker has failed to progress through the      *)
(*     "RECV_SUBMIT_HASH" state (i.e. data not successfully submitted)     *)
(*                                                                         *)
(*  - A Worker has accepted a task for which the Proving Deadline (Pd)     *)
(*     has elapsed, but the Worker has failed to progress through the      *)
(*     "RECV_SUBMIT_EVAL" state (i.e. evaluation not submitted)            *)
(*                                                                         *)
(* In either circumstance, the Worker resets and transitions to the next   *)
(* confirmed task (or re-queries TSC) via the logic defined in "NextTask". *)
(***************************************************************************)
TaskTimeout_IsEnabled(i) == 
    /\ Workers[i].currentTask # NULL
    \* Case 1: Submission not complete before Submission deadline
    /\ \/ /\ Workers[i].currentTask.Sd
          /\ Workers[i].state \in {"RECV_SEND_KEY", 
                                   "COMPUTE",
                                   "SEND_SUBMIT_DATA", 
                                   "RECV_SUBMIT_DATA", 
                                   "SEND_SUBMIT_HASH", 
                                   "RECV_SUBMIT_HASH"}  
       \* Case 2: Evaluation not complete before Proving deadline
       \/ /\ Workers[i].currentTask.Pd
          /\ Workers[i].state \in {"RECV_WEIGHTS",
                                   "SEND_QUERY_DATA", 
                                   "RECV_QUERY_DATA",
                                   "VERIFY",
                                   "REQUEST_DATA",
                                   "RECV_DATA",
                                   "SEND_SUBMIT_EVAL",
                                   "RECV_SUBMIT_EVAL"}
    
TaskTimeout(i) == 
    /\ TaskTimeout_IsEnabled(i) 
    /\ LET newTasks == Workers[i].confirmedTasks \ {Workers[i].currentTask}
           nextTask == IF Cardinality(newTasks) = 0 THEN NULL ELSE 
                       CHOOSE t \in newTasks : \A y \in newTasks : 
                              t.taskId # y.taskId => t.taskId < y.taskId   
       IN Workers' = [Workers EXCEPT 
           ![i].state = IF nextTask = NULL THEN "SEND_QUERY_TASKS" ELSE "GET_KEY",
           ![i].currentTask = nextTask,
           ![i].confirmedTasks = newTasks,
           ![i].requesterSk = NULL, 
           ![i].currentHash = NULL]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(* RandomCrash: This action simulates a random malfunction, via which a    *)
(* Worker terminates prior to completing its processing. Other parties     *)
(* must properly handle the loss of a Worker under any circumstances.      *)  
(***************************************************************************)
RandomCrash(i) == 
    /\ Workers[i].state # "TERMINATED"
    /\ Workers' = [Workers EXCEPT ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

(***************************************************************************)
(* Terminating: Allows all Workers to remain terminated indefinitely,      *)
(* required by TLA+ for stuttering.                                        *)
(***************************************************************************)
Terminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage>> 

(***************************************************************************)
(*                            ACTION DEFINITIONS                           *)
(***************************************************************************)        
Next == 
    \/ \E worker \in 1..NumWorkers : 
        \/ SendRegister(worker)
        \/ SendQueryTasks(worker)
        \/ SendConfirmTask(worker) 
        \/ SendSubmitData(worker) 
        \/ SendSubmitHash(worker)
        \/ SendQueryData(worker)
        \/ SendData(worker)
        \/ SendSubmitEval(worker)
        \/ Compute(worker)
        \/ Verify(worker)
        \/ RequestData(worker)     
        \/ ReceiveRegister(worker)
        \/ ReceiveRegister_Timeout(worker)
        \/ ReceiveQueryTasks(worker)
        \/ ReceiveQueryTasks_Timeout(worker)
        \/ ReceiveConfirmTask(worker)
        \/ ReceiveConfirmTask_Timeout(worker)
        \/ ReceiveSendKey(worker)
        \/ ReceiveSendKey_Timeout(worker)
        \/ ReceiveSubmitData(worker)
        \/ ReceiveSubmitData_Timeout(worker)
        \/ ReceiveSubmitHash(worker)
        \/ ReceiveSubmitHash_Timeout(worker)
        \/ ReceiveWeights(worker)
        \/ ReceiveWeights_Timeout(worker)
        \/ ReceiveQueryData(worker)
        \/ ReceiveQueryData_Timeout(worker)
        \/ ReceiveData(worker)
        \/ ReceiveData_Timeout(worker)
        \/ ReceiveSubmitEval(worker)
        \/ ReceiveSubmitEval_Timeout(worker)
        \/ EarlyTermination(worker)
        \/ TaskTimeout(worker)
        \/ RandomCrash(worker)
    \/ Terminating
        
=============================================================================
\* Modification History
\* Last modified Tue Mar 19 12:07:01 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
