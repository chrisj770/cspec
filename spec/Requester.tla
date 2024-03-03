----------------------------- MODULE Requester -----------------------------
EXTENDS FiniteSets, Sequences, TLC, Common

CONSTANT Tasks

RequiredTaskFields == {
    "id",               \* Unique identifier (starting at 1..)
    "Sd",               \* Submission deadline (time in steps)
    "Pd",               \* Proving deadline (time, in steps)
    "Td",               \* Task deadline (time, in steps)
    "numParticipants"}  \* Required number of participants

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
                 
CATDAlgorithm(i) == 
    {[address |-> w, weight |-> "placeholder"] :
     w \in Requesters[i].currentTask.participants}
           
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
(*                     SEND_REGISTER / RECV_REGISTER                       *)
(***************************************************************************)
SendRegister_IsEnabled(i) ==
    /\ Requesters[i].state = "SEND_REGISTER"
            
SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                   userType |-> "REQUESTER", 
                       from |-> i]
       IN /\ SendMessage(USCs.pk, request) 
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, TSCs, Storage>>

ReceiveRegister_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = USCs.pk
    /\ msg.type \in {"REGISTERED", "NOT_REGISTERED"}
    /\ msg.type = "REGISTERED" => \A f \in {"key", "pk", "sk"}: f \in DOMAIN msg

ReceiveRegister_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_REGISTER"
    /\ \E msg \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, msg)
    
ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
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
    
(***************************************************************************)
(*                    SEND_POST_TASKS / RECV_POST_TASKS                    *)
(***************************************************************************)
SendPostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    
SendPostTasks(i) == 
    /\ SendPostTasks_IsEnabled(i) 
    /\ LET request == [type |-> "POST_TASKS", 
                       from |-> Requesters[i].pk, 
                      tasks |-> Requesters[i].unpostedTasks]
       IN /\ SendMessage(TSCs.pk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, USCs, Storage>>

ReceivePostTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "INVALID", "NOT_REGISTERED"}

ReceivePostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_POST_TASKS"
    /\ \E msg \in Requesters[i].msgs: ReceivePostTasks_MessageFormat(i, msg)
    
ReceivePostTasks(i) == 
    /\ ReceivePostTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceivePostTasks_MessageFormat(i, m) 
       IN \/ /\ msg.type = "ACK"
             /\ Requesters' = [Requesters EXCEPT ![i].state = "SEND_QUERY_TASKS",
                                                 ![i].msgs = Requesters[i].msgs \ {msg}]
          \/ /\ msg.type # "ACK"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, USCs, TSCs, Storage>>

(***************************************************************************)
(*                   SEND_QUERY_TASKS / RECV_QUERY_TASKS                   *)
(***************************************************************************)
SendQueryTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_TASKS"
    
SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                       from |-> Requesters[i].pk, 
                      owner |-> Requesters[i].pk]
       IN /\ SendMessage(TSCs.pk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, USCs, Storage>>
     
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"TASKS", "INVALID", "NOT_REGISTERED"}
    /\ msg.type = "TASKS" => "tasks" \in DOMAIN msg

ReceiveQueryTasks_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Requesters[i].msgs: ReceiveQueryTasks_MessageFormat(i, msg)
    
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
                                    ![i].state = "SEND_QUERY_TASKS"]
    \/ /\ Cardinality(msg.tasks) = 0 
       /\ Terminate(i, msg)
     
ReceiveQueryTasks(i) == 
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryTasks_MessageFormat(i, m) 
       IN \/ /\ msg.type = "TASKS"
             /\ ReceiveQueryTasks_Success(i, msg)
          \/ /\ msg.type = "INVALID"
             /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                 ![i].state = "SEND_QUERY_TASKS"]
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                           SEND_KEY / RECV_KEY                           *)
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
       IN /\ SendMessage(nextWorkerPk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_KEY"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>

ReceiveKey_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ \E k \in Requesters[i].unconfirmedWorkers : k = msg.from     
    /\ msg.type = "ACK" 
    /\ msg.task = Requesters[i].currentTask.address

ReceiveKey_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_KEY"
    /\ Requesters[i].currentTask # NULL    
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ \E msg \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, msg)
    /\ ~Requesters[i].currentTask.Sd
    
ReceiveKey(i) == 
    /\ ReceiveKey_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, m) 
           worker == CHOOSE w \in Requesters[i].unconfirmedWorkers : w = msg.from 
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].unconfirmedWorkers = Requesters[i].unconfirmedWorkers \ {worker},
                                           ![i].confirmedWorkers = Requesters[i].confirmedWorkers \union {worker},
                                           ![i].state = IF Cardinality(Requesters[i].confirmedWorkers) + 1 = 
                                                           Cardinality(Requesters[i].currentTask.participants)
                                                        THEN "SEND_QUERY_HASHES"
                                                        ELSE "SEND_KEY"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                  SEND_QUERY_HASHES / RECV_QUERY_HASHES                  *)
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
       IN /\ SendMessage(TSCs.pk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_HASHES"]
    /\ UNCHANGED <<Workers, USCs, Storage>>
    
ReceiveQueryHashes_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"HASHES", "INVALID", "CANCELED", "COMPLETED", "NOT_REGISTERED"}
    /\ "task" \in DOMAIN msg => msg.type \in {"INVALID", "CANCELED", "COMPLETED", "HASHES"} 
    /\ "hashes" \in DOMAIN msg => msg.type = "HASHES" 

ReceiveQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_QUERY_HASHES"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.numParticipants = Cardinality(Requesters[i].confirmedWorkers)
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, msg)
    /\ ~Requesters[i].currentTask.Pd

ReceiveQueryHashes(i) == 
    /\ ReceiveQueryHashes_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, m)
       IN \/ /\ msg.type = "HASHES"
             /\ IF Cardinality(msg.hashes) = Requesters[i].currentTask.numParticipants
                THEN Requesters' = [Requesters EXCEPT 
                                        ![i].msgs = Requesters[i].msgs \ {msg},
                                        ![i].state = "SEND_QUERY_DATA", 
                                        ![i].submittedHashes = msg.hashes]
                ELSE Requesters' = [Requesters EXCEPT
                                        ![i].msgs = Requesters[i].msgs \ {msg},
                                        ![i].state = "SEND_QUERY_HASHES"] 
          \/ /\ msg.type = "INVALID"
             /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                 ![i].state = "SEND_QUERY_HASHES"]
          \/ /\ msg.type \in {"CANCELED", "COMPLETED"}
             /\ NextTask(i, msg)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                    SEND_QUERY_DATA / RECV_QUERY_DATA                    *)
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
       IN /\ SendMessage(Storage.pk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Workers, TSCs, USCs>> 
    
ReceiveQueryData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "allData"} : f \in DOMAIN msg
    /\ msg.from = Storage.pk
    /\ msg.type = "DATA"

ReceiveQueryData_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_DATA"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, msg)
    /\ ~Requesters[i].currentTask.Pd

ReceiveQueryData(i) == 
    /\ ReceiveQueryData_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, m)
           decryptedData == {[address |-> d.address,
                           submission |-> Decrypt(d.submission, Requesters[i].sk @@ 
                                                  [share |-> d.submission.encryptionKey.share])]
                            : d \in msg.allData}
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].submittedData = decryptedData,
                                           ![i].state = "EVALUATE"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                                EVALUATE                                 *)
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
(*                   SEND_SUBMIT_EVAL / RECV_SUBMIT_EVAL                   *)
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
       IN /\ SendMessage(TSCs.pk, request) 
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_SUBMIT_EVAL"]
    /\ UNCHANGED <<Workers, USCs, Storage>> 

ReceiveSubmitEval_MessageFormat(i, msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "INVALID", "CANCELED", "COMPLETED", "NOT_REGISTERED"}

ReceiveSubmitEval_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_SUBMIT_EVAL" 
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ \E msg \in Requesters[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg)
    /\ ~Requesters[i].currentTask.Pd 
    
ReceiveSubmitEval(i) ==
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveSubmitEval_MessageFormat(i, m)
       IN \/ /\ msg.type = "ACK"
             /\ Requesters' = [Requesters EXCEPT ![i].state = "SEND_WEIGHTS", 
                                                 ![i].msgs = Requesters[i].msgs \ {msg}]
          \/ /\ msg.type = "INVALID"
             /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                 ![i].state = "SEND_SUBMIT_EVAL"]
          \/ /\ msg.type \in {"CANCELED", "COMPLETED"}
             /\ NextTask(i, msg)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>

(***************************************************************************)
(*                        SEND_WEIGHTS / RECV_WEIGHTS                      *)
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
       IN /\ SendMessage(nextWorkerPk, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_WEIGHTS"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>
    
ReceiveWeights_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ \E w \in Requesters[i].confirmedWorkers : w = msg.from
    /\ msg.type = "ACK"
    /\ msg.task = Requesters[i].currentTask.address

ReceiveWeights_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_WEIGHTS"
    /\ Requesters[i].currentTask # NULL 
    /\ Requesters[i].confirmedWorkers # {} 
    /\ \E msg \in Requesters[i].msgs : ReceiveWeights_MessageFormat(i, msg)
    /\ ~Requesters[i].currentTask.Pd
    
ReceiveWeights(i) == 
    /\ ReceiveWeights_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveWeights_MessageFormat(i, m) 
           worker == CHOOSE w \in Requesters[i].confirmedWorkers : w = msg.from
       IN IF Cardinality(Requesters[i].confirmedWorkers) = 1
          THEN NextTask(i, msg)
          ELSE Requesters' = [Requesters EXCEPT 
                      ![i].msgs = Requesters[i].msgs \ {msg}, 
                      ![i].confirmedWorkers = Requesters[i].confirmedWorkers \ {worker},
                      ![i].state = "SEND_WEIGHTS"]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                     AUTOMATIC TIMEOUTS & TERMINATION                    *)
(***************************************************************************)    
IsPastFinalTaskDeadline(i) == 
    \A j \in 1..Len(Requesters[i].unpostedTasks) : 
        Requesters[i].unpostedTasks[j].Td = TRUE   
    
EarlyTermination_IsEnabled(i) == 
    \/ /\ Requesters[i].state = "SEND_REGISTER"      \* Case 1: No tasks to submit prior to registration     
       /\ Len(Requesters[i].unpostedTasks) = 0 
    \/ /\ Len(Requesters[i].unpostedTasks) > 0
       /\ IsPastFinalTaskDeadline(i)                 \* Case 2: Registration/Post not finished before final Task deadline
       /\ Requesters[i].state \in {"RECV_REGISTER",
                                   "RECV_POST_TASKS", 
                                   "RECV_QUERY_TASKS"}
                            
EarlyTermination(i) == 
    /\ EarlyTermination_IsEnabled(i) 
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>> 
        
TaskTimeout_IsEnabled(i) == 
    /\ Requesters[i].currentTask # NULL
    /\ \/ /\ Requesters[i].currentTask.Sd           \* Case 1: Keys not sent/ACKed before Submission deadline
          /\ Requesters[i].state \in {"SEND_KEY", 
                                      "RECV_KEY"}  
       \/ /\ Requesters[i].currentTask.Pd           \* Case 2: Evaluation not complete before Proving deadline
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
    
GlobalTimeout == 
    /\ Time >= MaxTime
    /\ Requesters' = [r \in 1..NumRequesters |-> [Requesters[r] EXCEPT !.state = "TERMINATED"]]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage>>
    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage>> 
            
Next == 
    \/ /\ Time < MaxTime
       /\ \E requester \in 1..NumRequesters : 
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
           \/ ReceivePostTasks(requester)
           \/ ReceiveQueryTasks(requester)
           \/ ReceiveKey(requester)
           \/ ReceiveQueryHashes(requester)
           \/ ReceiveQueryData(requester)
           \/ ReceiveSubmitEval(requester)
           \/ ReceiveWeights(requester)
           \/ EarlyTermination(requester)
           \/ TaskTimeout(requester)
    \/ GlobalTimeout
    \/ Terminating
    
=============================================================================
\* Modification History
\* Last modified Sat Mar 02 17:36:29 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
