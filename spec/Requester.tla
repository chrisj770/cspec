----------------------------- MODULE Requester -----------------------------
EXTENDS FiniteSets, Sequences, TLC, Common

RequiredTaskFields == {
    "id",               \* Unique identifier (starting at 1..)
    "Sd",               \* Submission deadline (time in steps)
    "Pd",               \* Proving deadline (time, in steps)
    "Td",               \* Task deadline (time, in steps)
    "numParticipants"}  \* Required number of participants

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init == 
    Requesters = [r \in 1..NumRequesters |-> [
                    msgs |-> {}, 
                   state |-> "SEND_REGISTER",
                 address |-> "",
                      pk |-> NULL, 
                      sk |-> NULL,
           unpostedTasks |-> Tasks,
                   tasks |-> {},
             currentTask |-> NULL,
      unconfirmedWorkers |-> {}, 
        confirmedWorkers |-> {},
         submittedHashes |-> {},
           submittedData |-> {},
                 weights |-> {}]]

(***************************************************************************)
(* CATDAlgorithm: This operator is invoked during a Requester's "EVALUATE" *)
(* stage to simulate evaluation of received data. (NOTE: An implementation *)
(* of an actual truth-discovery algorithm is not included, as this remains *)
(* out-of-scope for this specification.)                                   *)
(***************************************************************************)                 
CATDAlgorithm(i) == 
    {[address |-> w, weight |-> "placeholder"] :
     w \in Requesters[i].currentTask.participants}

(***************************************************************************)
(* Terminate: This operator is invoked under a variety of circumstances,   *)
(* upon which a Requester transitions to state "TERMINATED" and remains    *)
(* idle indefinitely until all processing ceases.                          *) 
(***************************************************************************)             
Terminate(i, msg) == 
    Requesters' = [Requesters EXCEPT 
            ![i].msgs = IF msg # NULL 
                    THEN Requesters[i].msgs \ {msg}
                    ELSE Requesters[i].msgs,
            ![i].state = "TERMINATED", 
            ![i].currentTask = NULL,
            ![i].unconfirmedWorkers = {},
            ![i].confirmedWorkers = {}, 
            ![i].submittedHashes  = {},
            ![i].submittedData = {}, 
            ![i].weights = {}]

(***************************************************************************)
(* NextTask: This operator is invoked when (1) a task is successfully      *)
(* completed via the "RECV_SUBMIT_EVAL" state, (2) a message timeout has   *)
(* occurred in any "RECV" state, or (3) a task timeout has occurred due to *)
(* the Submission/Proving deadline elapsing before all necessary Requester *)
(* actions have been completed.                                            *)
(*                                                                         *)
(* If 1+ confirmed tasks remain, set "currentTask" to the next confirmed   *)
(* task (w/ lowest "taskId") and transition to state "SEND_KEY". If 0      *)
(* confirmed tasks remain, terminate immediately.                          *)
(***************************************************************************)
GetNextTask(i) == 
    IF Cardinality(Requesters[i].tasks) = 0 THEN NULL 
    ELSE CHOOSE t \in Requesters[i].tasks : \A y \in Requesters[i].tasks : 
                t.taskId # y.taskId => t.taskId < y.taskId  
           
NextTask(i, msg) == 
    LET nextTask == GetNextTask(i) 
    IN IF nextTask = NULL 
       THEN Terminate(i, msg)
       ELSE Requesters' = [Requesters EXCEPT 
           ![i].state = "SEND_KEY",
           ![i].msgs = Requesters[i].msgs \ {msg},
           ![i].tasks = Requesters[i].tasks \ {nextTask},
           ![i].currentTask = nextTask,
           ![i].unconfirmedWorkers = nextTask.participants,
           ![i].confirmedWorkers = {}, 
           ![i].submittedHashes  = {},
           ![i].submittedData = {}, 
           ![i].weights = {}]

(***************************************************************************)
(*                             SEND_REGISTER                               *)
(*                                                                         *)
(* Send "REGISTER" message to USC to register as a Requester, then         *)
(* transition immediately to "RECV_REGISTER" upon completion.              *)
(***************************************************************************)
SendRegister_IsEnabled(i) ==
    /\ Requesters[i].state = "SEND_REGISTER"
            
SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                   userType |-> "REQUESTER", 
                       from |-> i]
       IN /\ SendUSCMessage(request) 
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, TSCs, Storage>>

(***************************************************************************)
(*                             RECV_REGISTER                               *)
(*                                                                         *)
(* Await "REGISTERED" message from USC with address and private/public     *)
(* key-share, indicating that the Requester has been successfully          *)
(* registered. Transition to "SEND_POST_TASKS" upon receipt of expected    *)
(* message, or terminate early upon timeout or receipt of "NOT_REGISTERED".*)
(***************************************************************************)
ReceiveRegister_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = USCs.pk
    /\ msg.type \in {"REGISTERED", "NOT_REGISTERED"}
    /\ msg.type = "REGISTERED" => \A f \in {"key", "pk", "sk"}: f \in DOMAIN msg

ReceiveRegister_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_REGISTER"
    
ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, m) 
       IN \/ /\ msg.type = "REGISTERED" 
             /\ Requesters' = [Requesters EXCEPT ![i].address = msg.key,
                                                 ![i].pk = msg.pk,
                                                 ![i].sk = msg.sk,
                                                 ![i].msgs = Requesters[i].msgs \ {msg}, 
                                                 ![i].state = "SEND_POST_TASKS"]
          \/ /\ msg.type # "REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, USCs, TSCs, Storage>>
    
ReceiveRegister_Timeout(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, msg))
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                             SEND_POST_TASKS                             *)
(*                                                                         *)
(* Send "POST_TASKS" message to TSC containing list of tasks to be posted, *)
(* then transition immediately to "RECV_POST_TASKS" upon completion.       *)
(***************************************************************************)
SendPostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    
SendPostTasks(i) == 
    /\ SendPostTasks_IsEnabled(i) 
    /\ LET request == [type |-> "POST_TASKS", 
                       from |-> Requesters[i].pk, 
                      tasks |-> Requesters[i].unpostedTasks]
       IN /\ SendTSCMessage(request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, USCs, Storage>>

(***************************************************************************)
(*                             RECV_POST_TASKS                             *)
(*                                                                         *)
(* Await "ACK" message from TSC indicating successful receipt of tasks.    *)
(* Upon receiving the expected message, transition to "SEND_QUERY_TASKS".  *)
(* If a timeout occurs, terminate immediately.                             *)
(***************************************************************************)
ReceivePostTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "NOT_REGISTERED"}

ReceivePostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_POST_TASKS"
    
ReceivePostTasks(i) == 
    /\ ReceivePostTasks_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs: ReceivePostTasks_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceivePostTasks_MessageFormat(i, m) 
       IN \/ /\ msg.type = "ACK"
             /\ Requesters' = [Requesters EXCEPT ![i].state = "SEND_QUERY_TASKS",
                                                 ![i].msgs = Requesters[i].msgs \ {msg}]
          \/ /\ msg.type # "ACK"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, USCs, TSCs, Storage>>
    
ReceivePostTasks_Timeout(i) == 
    /\ ReceivePostTasks_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs: ReceivePostTasks_MessageFormat(i, msg))
    /\ Terminate(i, NULL) 
    /\ UNCHANGED <<Workers, USCs, TSCs, Storage>>    
    
(***************************************************************************)
(*                            SEND_QUERY_TASKS                             *)
(*                                                                         *)
(* Send "QUERY_TASKS" message to TSC to retrive a list of posted tasks for *)
(* which the Requester is registered as an "owner", then transition        *)
(* immediately to "RECV_QUERY_TASKS" upon completion.                      *)
(***************************************************************************)
SendQueryTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_TASKS"
    
SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                       from |-> Requesters[i].pk, 
                      owner |-> Requesters[i].pk]
       IN /\ SendTSCMessage(request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, USCs, Storage>>
    
(***************************************************************************)
(*                            RECV_QUERY_TASKS                             *)
(*                                                                         *)
(* Await "TASKS" message from TSC containing a list of posted tasks for    *)
(* which the Requester is registed as an "owner". Upon receiving the       *)
(* expected message, perform a state transition based on the following     *)
(* conditions:                                                             *)
(*                                                                         *)
(*  - If the list is non-empty and all tasks have state="Unavailable",     *)
(*     set the "currentTask" as the task with the lowest "taskId" and      *)
(*     transition to "SEND_KEY".                                           *)
(*                                                                         *)
(*  - If the list is non-empty and all tasks have state "Canceled" or      *)
(*     "Completed", terminate immediately.                                 *)
(*                                                                         *)
(*  - If the list is non-empty and any task has state "Available" or       *)
(*     "QEvaluating", transition to "SEND_QUERY_TASKS" and repeat the      *)
(*     query. (NOTE: This will not occur in-practice, as the TSC only      *)
(*     sends "TASKS" to Requesters when all tasks are "Unavailable".)      *)
(*                                                                         *)
(*  - If the list is empty, terminate immediately.                         *)
(*                                                                         *)
(* Alternatively, if a timeout occurs, terminate immediately.              *)
(***************************************************************************)     
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"TASKS", "NOT_REGISTERED"}
    /\ msg.type = "TASKS" => "tasks" \in DOMAIN msg

ReceiveQueryTasks_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_TASKS"
    
ReceiveQueryTasks_Success(i, msg) == 
    \/ /\ Cardinality(msg.tasks) > 0
       /\ \/ /\ \A t \in msg.tasks : t.owner = Requesters[i].pk => t.state = "Unavailable"
             /\ LET firstTask == CHOOSE t \in msg.tasks : \A y \in msg.tasks : 
                                 t.taskId # y.taskId => t.taskId < y.taskId 
                IN Requesters' = [Requesters EXCEPT 
                                    ![i].msgs = Requesters[i].msgs \ {msg},
                                    ![i].tasks = msg.tasks \ {firstTask},
                                    ![i].unconfirmedWorkers = firstTask.participants, 
                                    ![i].confirmedWorkers = {},
                                    ![i].unpostedTasks = <<>>,
                                    ![i].currentTask = firstTask,
                                    ![i].state = "SEND_KEY"]
          \/ /\ \A t \in msg.tasks : t.owner = Requesters[i].pk => t.state \in {"Canceled", "Completed"}
             /\ Terminate(i, msg)
          \/ /\ \E t \in msg.tasks : t.owner = Requesters[i].pk => t.state \in {"Available", "QEvaluating"}
             /\ Requesters' = [Requesters EXCEPT 
                                    ![i].msgs = Requesters[i].msgs \ {msg}, 
                                    ![i].state = "SEND_QUERY_TASKS",
                                    ![i].tasks = msg.tasks]
    \/ /\ Cardinality(msg.tasks) = 0 
       /\ Terminate(i, msg)
     
ReceiveQueryTasks(i) == 
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs: ReceiveQueryTasks_MessageFormat(i, msg)    
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryTasks_MessageFormat(i, m) 
       IN \/ /\ msg.type = "TASKS"
             /\ ReceiveQueryTasks_Success(i, msg)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveQueryTasks_Timeout(i) == 
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs: ReceiveQueryTasks_MessageFormat(i, msg))
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>> 

(***************************************************************************)
(*                                SEND_KEY                                 *)
(*                                                                         *)
(* For the next unconfirmed Worker in the "currentTask", generate the      *)
(* corresponding private key-share and send "SEND_KEY" message containing  *)
(* key-share to Worker, then immediately transition to "RECV_KEY" upon     *)
(* completion.                                                             *)
(***************************************************************************)
SendKey_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_KEY"
    /\ Requesters[i].currentTask # NULL
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ ~Requesters[i].currentTask.Sd

SendKey(i) ==
    /\ SendKey_IsEnabled(i)
    /\ LET nextWorkerPk == CHOOSE r \in Requesters[i].unconfirmedWorkers : TRUE
           splitkeyshare == Requesters[i].sk @@ 
                            [share |-> Requesters[i].currentTask.numParticipants - 
                                       Cardinality(Requesters[i].unconfirmedWorkers)]
           request == [type |-> "SEND_KEY", 
                       from |-> Requesters[i].pk, 
                       task |-> Requesters[i].currentTask.address,
                   keyshare |-> Encrypt(splitkeyshare, nextWorkerPk)]
       IN /\ SendWorkerMessage(nextWorkerPk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_KEY"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>

(***************************************************************************)
(*                                RECV_KEY                                 *)
(*                                                                         *)
(* Await "ACK" message from Worker indicating successful receipt of key-   *)
(* share. Upon receipt, either (1) transition to "SEND_KEY" if 1+          *)
(* unconfirmed Workers remain, or (2) transition to "SEND_QUERY_HASHES" if *)
(* 0 unconfirmed Workers remain.                                           *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or terminate immediately) via the logic defined in "NextTask".         *)
(***************************************************************************)
ReceiveKey_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ \E k \in Requesters[i].unconfirmedWorkers : k = msg.from     
    /\ msg.type = "ACK" 
    /\ msg.task = Requesters[i].currentTask.address

ReceiveKey_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_KEY"
    /\ Requesters[i].currentTask # NULL    
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ ~Requesters[i].currentTask.Sd
    
ReceiveKey(i) == 
    /\ ReceiveKey_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, m) 
           worker == CHOOSE w \in Requesters[i].unconfirmedWorkers : w = msg.from 
       IN Requesters' = [Requesters EXCEPT 
            ![i].msgs = Requesters[i].msgs \ {msg},
            ![i].unconfirmedWorkers = Requesters[i].unconfirmedWorkers \ {worker},
            ![i].confirmedWorkers = Requesters[i].confirmedWorkers \union {worker},
            ![i].state = IF Cardinality(Requesters[i].confirmedWorkers) + 1 = 
                            Cardinality(Requesters[i].currentTask.participants)
                         THEN "SEND_QUERY_HASHES"
                         ELSE "SEND_KEY"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveKey_Timeout(i) == 
    /\ ReceiveKey_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                            SEND_QUERY_HASHES                            *)
(*                                                                         *)
(* Send "QUERY_HASHES" message to TSC to request a list of submitted       *)
(* hashes associated with the current task, then transition immediately to *)
(* "RECV_QUERY_HASHES" upon completion.                                    *)
(***************************************************************************)
SendQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_HASHES"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ ~Requesters[i].currentTask.Pd

SendQueryHashes(i) == 
    /\ SendQueryHashes_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_HASHES", 
                       from |-> Requesters[i].pk, 
                       task |-> Requesters[i].currentTask.address] 
       IN /\ SendTSCMessage(request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_HASHES"]
    /\ UNCHANGED <<Workers, USCs, Storage>>

(***************************************************************************)
(*                            RECV_QUERY_HASHES                            *)
(*                                                                         *)
(* Await "HASHES" message from TSC containing a list of submitted hashes   *)
(* associated with the current task. Upon receipt, store the hashes for    *) 
(* later processing and transition to "SEND_QUERY_DATA".                   *)
(*                                                                         *)
(* Upon receiving a message of type "CANCELED"/"COMPLETED" (or a timeout)  *)
(* reset and transition to the next confirmed task (or terminate           *)
(* immediately) via the logic defined in "NextTask".                       *)
(***************************************************************************)
ReceiveQueryHashes_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"HASHES", "CANCELED", "COMPLETED", "NOT_REGISTERED"}
    /\ "task" \in DOMAIN msg => msg.type \in {"CANCELED", "COMPLETED", "HASHES"} 
    /\ "hashes" \in DOMAIN msg => msg.type = "HASHES" 

ReceiveQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_QUERY_HASHES"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.numParticipants = Cardinality(Requesters[i].confirmedWorkers)
    /\ ~Requesters[i].currentTask.Pd

ReceiveQueryHashes(i) == 
    /\ ReceiveQueryHashes_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, m)
       IN \/ /\ msg.type = "HASHES"
             /\ Requesters' = [Requesters EXCEPT 
                                  ![i].msgs = Requesters[i].msgs \ {msg},
                                  ![i].state = "SEND_QUERY_DATA", 
                                  ![i].submittedHashes = msg.hashes]
          \/ /\ msg.type \in {"CANCELED", "COMPLETED"}
             /\ NextTask(i, msg)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveQueryHashes_Timeout(i) == 
    /\ ReceiveQueryHashes_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, msg))
    /\ NextTask(i, NULL) 
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                             SEND_QUERY_DATA                             *)
(*                                                                         *)
(* Send "QUERY_DATA" message to Storage containing the list of submitted   *)
(* hashes to query, then transition immediately to "RECV_QUERY_DATA" upon  *)
(* completion.                                                             *)
(***************************************************************************)
SendQueryData_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_DATA"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ ~Requesters[i].currentTask.Pd

SendQueryData(i) == 
    /\ SendQueryData_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_DATA", 
                       from |-> Requesters[i].pk, 
                     hashes |-> Requesters[i].submittedHashes]
       IN /\ SendStorageMessage(request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Workers, TSCs, USCs>> 

(***************************************************************************)
(*                             RECV_QUERY_DATA                             *)
(*                                                                         *)
(* Await "DATA" message from storage containing encrypted sensory data     *)
(* corresponding to all hashes requested in the "QUERY_DATA" message.      *)
(* Upon receipt, decrypt all data via the Requester's private key, store   *)
(* the data for later processing, then transition to "EVALUATE".           *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or terminate immediately) via the logic defined in "NextTask".         *)
(***************************************************************************)
ReceiveQueryData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "allData"} : f \in DOMAIN msg
    /\ msg.from = Storage.pk
    /\ msg.type = "DATA"

ReceiveQueryData_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_DATA"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ ~Requesters[i].currentTask.Pd

ReceiveQueryData(i) == 
    /\ ReceiveQueryData_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, m)
           decryptedData == {[address |-> d.address,
                           submission |-> Decrypt(d.submission, Requesters[i].sk @@ 
                                                  [share |-> d.submission.encryptionKey.share])]
                            : d \in msg.allData}
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].submittedData = decryptedData,
                                           ![i].state = "EVALUATE"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveQueryData_Timeout(i) ==
    /\ ReceiveQueryData_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                                EVALUATE                                 *)
(*                                                                         *)
(* Run CATD Algorithm on all sensory data received from Storage, then      *)
(* store results for later processing and transition immediately to        *) 
(* "SEND_SUBMIT_EVAL" upon completion.                                     *)
(***************************************************************************)
Evaluate_IsEnabled(i) == 
    /\ Requesters[i].state = "EVALUATE"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ Cardinality(Requesters[i].submittedData) = Requesters[i].currentTask.numParticipants
    /\ ~Requesters[i].currentTask.Pd
 
Evaluate(i) ==
    /\ Evaluate_IsEnabled(i) 
    /\ LET weights == CATDAlgorithm(i)
       IN /\ Requesters' = [Requesters EXCEPT ![i].state = "SEND_SUBMIT_EVAL", 
                                              ![i].weights = weights] 
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                            SEND_SUBMIT_EVAL                             *)
(*                                                                         *)
(* Send "SUBMIT_EVAL" message to TSC containing evaluation results, then   *)
(* transition immediately to "RECV_SUBMIT_EVAL" upon completion.           *)
(***************************************************************************)
SendSubmitEval_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_SUBMIT_EVAL"
    /\ Requesters[i].currentTask # NULL 
    /\ Requesters[i].weights # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ Cardinality(Requesters[i].submittedData) = Requesters[i].currentTask.numParticipants
    /\ ~Requesters[i].currentTask.Pd

SendSubmitEval(i) == 
    /\ SendSubmitEval_IsEnabled(i) 
    /\ LET request == [type |-> "SUBMIT_EVAL",
                       from |-> Requesters[i].pk,
                       task |-> Requesters[i].currentTask.address,
                    weights |-> Requesters[i].weights]
       IN /\ SendTSCMessage(request) 
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_SUBMIT_EVAL"]
    /\ UNCHANGED <<Workers, USCs, Storage>> 

(***************************************************************************)
(*                            RECV_SUBMIT_EVAL                             *)
(*                                                                         *)
(* Await "ACK" message from TSC indicating successful receipt of           *)
(* evaluation results. Upon receipt, transition to "SEND_WEIGHTS".         *)        
(*                                                                         *)
(* Upon receiving a message of type "CANCELED"/"COMPLETED" (or a timeout)  *)
(* reset and transition to the next confirmed task (or terminate           *)
(* immediately) via the logic defined in "NextTask".                       *)
(***************************************************************************)
ReceiveSubmitEval_MessageFormat(i, msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "CANCELED", "COMPLETED", "NOT_REGISTERED"}

ReceiveSubmitEval_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_SUBMIT_EVAL" 
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ ~Requesters[i].currentTask.Pd 
    
ReceiveSubmitEval(i) ==
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveSubmitEval_MessageFormat(i, m)
       IN \/ /\ msg.type = "ACK"
             /\ Requesters' = [Requesters EXCEPT ![i].state = "SEND_WEIGHTS", 
                                                 ![i].msgs = Requesters[i].msgs \ {msg}]
          \/ /\ msg.type \in {"CANCELED", "COMPLETED"}
             /\ NextTask(i, msg)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveSubmitEval_Timeout(i) == 
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                               SEND_WEIGHTS                              *)
(*                                                                         *)
(* For next confirmed Worker, send "WEIGHTS" message containing evaluation *)
(* results to Worker, then transition immediately to "RECV_WEIGHTS" upon   *)
(* completion.                                                             *)
(***************************************************************************)
SendWeights_IsEnabled(i) ==
    /\ Requesters[i].state = "SEND_WEIGHTS"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].confirmedWorkers # {} 
    /\ ~Requesters[i].currentTask.Pd

SendWeights(i) == 
    /\ SendWeights_IsEnabled(i)
    /\ LET nextWorkerPk == CHOOSE r \in Requesters[i].confirmedWorkers : TRUE
           request == [type |-> "WEIGHTS", 
                       from |-> Requesters[i].pk, 
                    weights |-> Requesters[i].weights,
                       task |-> Requesters[i].currentTask.address]
       IN /\ SendWorkerMessage(nextWorkerPk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_WEIGHTS"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>

(***************************************************************************)
(*                               SEND_WEIGHTS                              *)
(*                                                                         *)
(* Await "ACK" message from Worker indicating successful receipt of        *)
(* evaluation results. Upon receipt, remove the Worker from the list of    *) 
(* confirmed Workers to prevent from repeating the same request, then      *)
(* either (1) transition to "SEND_WEIGHTS" if 1+ confirmed Workers remain, *)
(* or (2) reset and transition to the next confirmed task (or terminate    *)
(* immediately) via the logic defined in "NextTask" if 0 confirmed Workers *)
(* remain.                                                                 *)
(*                                                                         *)
(* If a timeout occurs, reset and transition to the next confirmed task    *)
(* (or terminate immediately) via the logic defined in "NextTask".         *)
(***************************************************************************)
ReceiveWeights_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ \E w \in Requesters[i].confirmedWorkers : w = msg.from
    /\ msg.type = "ACK"
    /\ msg.task = Requesters[i].currentTask.address

ReceiveWeights_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_WEIGHTS"
    /\ Requesters[i].currentTask # NULL 
    /\ Requesters[i].confirmedWorkers # {} 
    /\ ~Requesters[i].currentTask.Pd
    
ReceiveWeights(i) == 
    /\ ReceiveWeights_IsEnabled(i)
    /\ \E msg \in Requesters[i].msgs : ReceiveWeights_MessageFormat(i, msg)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveWeights_MessageFormat(i, m) 
           worker == CHOOSE w \in Requesters[i].confirmedWorkers : w = msg.from
       IN IF Cardinality(Requesters[i].confirmedWorkers) = 1
          THEN NextTask(i, msg)
          ELSE Requesters' = [Requesters EXCEPT 
                      ![i].msgs = Requesters[i].msgs \ {msg}, 
                      ![i].confirmedWorkers = Requesters[i].confirmedWorkers \ {worker},
                      ![i].state = "SEND_WEIGHTS"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
ReceiveWeights_Timeout(i) == 
    /\ ReceiveWeights_IsEnabled(i)
    /\ ~(\E msg \in Requesters[i].msgs : ReceiveWeights_MessageFormat(i, msg))
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>    
    
(***************************************************************************)
(* EarlyTermination: This action is invoked when a Requester either (1)    *) 
(* possesses no tasks to submit prior to Registration, or (2) has failed   *)
(* to progress through the "RECV_QUERY_TASKS" state (i.e. receive a task   *)
(* list for which all tasks have state="Unavailable") before its final     *) 
(* task deadline elapses. In this case, the Requester terminates           *) 
(* immediately w/o further processing.                                     *) 
(***************************************************************************)    
IsPastFinalTaskDeadline(i) == 
    \A j \in 1..Len(Requesters[i].unpostedTasks) : 
        Requesters[i].unpostedTasks[j].Td = TRUE   
    
EarlyTermination_IsEnabled(i) == 
    \* Case 1: No tasks to submit prior to registration
    \/ /\ Requesters[i].state = "SEND_REGISTER"           
       /\ Len(Requesters[i].unpostedTasks) = 0 
    \* Case 2: Registration/Post not finished before final Task deadline
    \/ /\ Len(Requesters[i].unpostedTasks) > 0
       /\ IsPastFinalTaskDeadline(i)                 
       /\ Requesters[i].state \in {"RECV_REGISTER",
                                   "RECV_POST_TASKS", 
                                   "RECV_QUERY_TASKS"}
                            
EarlyTermination(i) == 
    /\ EarlyTermination_IsEnabled(i) 
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>> 

(***************************************************************************)
(* TaskTimeout: This action is invoked under the following conditions:     *)
(*                                                                         *)
(*  - A Requester is operating upon a task for which the Submission        *)
(*     Deadline (Sd) has elapsed, but the Requester has failed to          *)
(*     progress through the "SEND_KEY"/"RECV_KEY" states (i.e. key-shares  *)
(*     not successfully distributed)                                       *)
(*                                                                         *)
(*  - A Requester is operating upon a task for which the Proving           *)
(*     Deadline (Pd) has elapsed, but the Requester has failed to          *)
(*     progress through the "RECV_WEIGHTS" state (i.e. evaluation results  *)
(*     not successfully distributed)                                       *)
(*                                                                         *)
(* In either circumstance, the Requester resets and transitions to the     *)
(* next confirmed task (or terminates immediately) via the logic defined   *)
(* in "NextTask".                                                          *)
(***************************************************************************)
TaskTimeout_IsEnabled(i) == 
    /\ Requesters[i].currentTask # NULL
    \* Case 1: Keys not sent/ACKed before Submission deadline
    /\ \/ /\ Requesters[i].currentTask.Sd           
          /\ Requesters[i].state \in {"SEND_KEY", 
                                      "RECV_KEY"}
       \* Case 2: Evaluation not complete before Proving deadline  
       \/ /\ Requesters[i].currentTask.Pd           
          /\ Requesters[i].state \in {"SEND_QUERY_HASHES",  
                                      "RECV_QUERY_HASHES",
                                      "SEND_QUERY_DATA",
                                      "RECV_QUERY_DATA",
                                      "EVALUATE",
                                      "SEND_SUBMIT_EVAL",
                                      "RECV_SUBMIT_EVAL",
                                      "SEND_WEIGHTS", 
                                      "RECV_WEIGHTS"}

TaskTimeout(i) == 
    /\ TaskTimeout_IsEnabled(i) 
    /\ NextTask(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
(***************************************************************************)
(* RandomCrash: This action simulates a random malfunction, via which a    *)
(* Requester terminates prior to completing its processing. Other parties  *)
(* must properly handle the loss of a Requester under any circumstances.   *)  
(***************************************************************************)
RandomCrash(i) == 
    /\ Requesters[i].state # "TERMINATED"
    /\ Requesters' = [Requesters EXCEPT ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(* Terminating: Allows all Requesters to remain terminated indefinitely,   *)
(* required by TLA+ for stuttering.                                        *)
(***************************************************************************)    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage>> 

(***************************************************************************)
(*                            ACTION DEFINITIONS                           *)
(***************************************************************************)             
Next == 
    \/ \E requester \in 1..NumRequesters : 
        \/ SendRegister(requester)
        \/ SendPostTasks(requester)
        \/ SendQueryTasks(requester)
        \/ SendKey(requester)
        \/ SendQueryHashes(requester)
        \/ SendQueryData(requester)
        \/ SendSubmitEval(requester)
        \/ Evaluate(requester)
        \/ SendWeights(requester)
        \/ ReceiveRegister(requester) 
        \/ ReceiveRegister_Timeout(requester)       
        \/ ReceivePostTasks(requester)
        \/ ReceivePostTasks_Timeout(requester)
        \/ ReceiveQueryTasks(requester)
        \/ ReceiveQueryTasks_Timeout(requester)
        \/ ReceiveKey(requester)
        \/ ReceiveKey_Timeout(requester)
        \/ ReceiveQueryHashes(requester)
        \/ ReceiveQueryHashes_Timeout(requester)
        \/ ReceiveQueryData(requester)
        \/ ReceiveQueryData_Timeout(requester)
        \/ ReceiveSubmitEval(requester)
        \/ ReceiveSubmitEval_Timeout(requester)
        \/ ReceiveWeights(requester)
        \/ ReceiveWeights_Timeout(requester)
        \/ EarlyTermination(requester)
        \/ TaskTimeout(requester)
        \/ RandomCrash(requester)
    \/ Terminating
    
=============================================================================
\* Modification History
\* Last modified Tue Mar 19 12:55:28 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
