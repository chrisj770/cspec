------------------------------- MODULE Worker -------------------------------
EXTENDS FiniteSets, Sequences, Common, TLC, Integers
    
CONSTANT TaskQueryDeadline    

TypeOK == 
    /\ \A worker \in Workers : [Workers.state -> 
        {"INIT",                \* Initialize local variables
         "SEND_REGISTER",       \* Attempt to register as a WORKER via USSC
         "RECV_REGISTER",       \* Receive acknowledgement and public/private key from USSC 
         "SEND_QUERY_TASKS",    \* Request list of active tasks via TSC
         "RECV_QUERY_TASKS",    \* Receive list of active tasks from TSC, or INVALID
         "SEND_CONFIRM_TASK",   \* Attempt to enlist as a confirmed WORKER for each selected TSC
         "RECV_SEND_KEY",       \* Await key-share from REQUESTER for single task
         "COMPUTE",             \* Generate sensory data
         "SEND_SUBMIT_DATA",    \* Attempt to submit encrypted sensory data to STORAGE
         "RECV_SUBMIT_DATA",    \* Receive acknowledgement for sensory data from STORAGE
         "SEND_SUBMIT_HASH",    \* Attempt to submit hash of sensory data to TSC
         "RECV_SUBMIT_HASH",    \* Receive acknowledgement for hash from TSC 
         "RECV_WEIGHTS",        \* Await weight broadcast from REQUESTER
         "SEND_QUERY_HASHES",   \* Request list of all hashes from TSC
         "RECV_QUERY_HASHES",   \* Receive list of all hashes from TSC
         "SEND_QUERY_DATA",     \* Request all relevant sensory data from STORAGE
         "SEND_QUERY_DATA",     \* Receive list of sensory data from STORAGE
         "VERIFY",              \* Run verification process
         "REQUEST_DATA", 
         "RECV_DATA",
         "SEND_SUBMIT_EVAL",    \* Attempt to submit evaluation results to TSC  
         "RECV_SUBMIT_EVAL",    \* Receive Acknowledgement for evaluation results from TSC
         "TERMINATED"}]         
                  
Init ==
    Workers = [w \in 1..NumWorkers |-> [
                  msgs |-> {},              \* Message queue 
                 state |-> "SEND_REGISTER", \* Current state
               address |-> "",              \* Address/Pseudonym
                    pk |-> NULL,            \* Public key (obtained from USC during registration)
                    sk |-> NULL,            \* Private key (obtained from USC during registration)
      unconfirmedTasks |-> {},              \* List of unconfirmed tasks (obtained from TSC during "RECV_QUERY_TASKS")
        confirmedTasks |-> {},              \* List of confirmed tasks (obtained via "CONFIRM_SUCCESS")
           currentTask |-> NULL,            \* Current task 
           requesterSk |-> NULL,            \* Partial private key-share (obtained from Requester during "RECV_SEND_KEY")
           currentHash |-> NULL,            \* Data hash (obtained via submitting data to STORAGE during "RECV_SUBMIT_DATA")
      requesterWeights |-> NULL,            \* Evaluated worker weights (obtained from Requester during "RECV_WEIGHTS")
      participantsSent |-> {},              \* Set of other workers for sending cyphertext
      participantsRcvd |-> {},              \* Set of other workers for receiving cyphertexts
         submittedData |-> {},              \* Set of data submitted by all workers (obtained from other workers during "VERIFY")
               weights |-> {}]] 

CATDAlgorithm(i) == 
    {[participant |-> w.address, weight |-> "placeholder"] :
     w \in Workers[i].submittedData}
     
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
(*                     SEND_REGISTER / RECV_REGISTER                       *)
(***************************************************************************)
SendRegister_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_REGISTER"

SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                   userType |-> "WORKER", 
                       from |-> i]
       IN /\ SendMessage(USCs.pk, request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Requesters, TSCs, Storage>>

ReceiveRegister_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = USCs.pk
    /\ msg.type \in {"REGISTERED", "NOT_REGISTERED"}
    /\ msg.type = "REGISTERED" \equiv \A f \in {"key", "pk", "sk"}: f \in DOMAIN msg

ReceiveRegister_IsEnabled(i) ==
    /\ Workers[i].state = "RECV_REGISTER"
    /\ \E msg \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, msg)

ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
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
    
(***************************************************************************)
(*                   SEND_QUERY_TASKS / RECV_QUERY_TASKS                   *)
(***************************************************************************)
SendQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_QUERY_TASKS"

SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                       from |-> Workers[i].pk,
                      owner |-> NULL]
       IN /\ SendMessage(TSCs.pk, request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>
    
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"TASKS", "INVALID", "NOT_REGISTERED"}
    /\ msg.type = "TASKS" \equiv "tasks" \in DOMAIN msg

ReceiveQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, msg)
    
ReceiveQueryTasks_Success(i, msg) == 
    LET validTasks == {t \in msg.tasks : t.state = "Available"}
    IN IF Cardinality(validTasks) = 0 
       THEN Terminate(i, msg)
       ELSE Workers' = [Workers EXCEPT 
                    ![i].msgs = Workers[i].msgs \ {msg},
                    ![i].unconfirmedTasks = validTasks,
                    ![i].state = "SEND_CONFIRM_TASK"]
    
ReceiveQueryTasks(i) ==
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, m)
       IN \/ /\ msg.type = "TASKS" 
             /\ ReceiveQueryTasks_Success(i, msg)
          \/ /\ msg.type # "TASKS"
             /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                           ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                  SEND_CONFIRM_TASK / RECV_CONFIRM_TASK                  *)
(***************************************************************************)
SendConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_CONFIRM_TASK" 

SendConfirmTask(i) == 
    /\ SendConfirmTask_IsEnabled(i)
    /\ LET nextConfTask == CHOOSE tsc \in Workers[i].unconfirmedTasks :
                           \A other \in Workers[i].unconfirmedTasks: 
                           tsc # other => tsc.taskId < other.taskId
           request == [type |-> "CONFIRM_TASK", 
                       from |-> Workers[i].pk, 
                       task |-> nextConfTask.address]
       IN /\ SendMessage(TSCs.pk, request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_CONFIRM_TASK"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>

ReceiveConfirmTask_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"CANCELED", "COMPLETED", "CONFIRM_FAIL", "CONFIRM_SUCCESS", "NOT_REGISTERED"}
    /\ msg.type \in {"CANCELED", "COMPLETED", "CONFIRM_FAIL", "CONFIRM_SUCCESS"} \equiv "task" \in DOMAIN msg

ReceiveConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_CONFIRM_TASK"
    /\ \E msg \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, msg)
    
ReceiveConfirmTask_Success(i, msg, task) == 
    LET finished == Cardinality(Workers[i].unconfirmedTasks) = 1 
        newTasks == Workers[i].confirmedTasks \union {task} 
        firstTask == CHOOSE t \in newTasks: \A y \in newTasks: 
                            t.taskId # y.taskId => t.taskId < y.taskId
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId}, 
                   ![i].confirmedTasks = IF finished THEN newTasks \ {firstTask} ELSE newTasks,
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN "RECV_SEND_KEY" ELSE "SEND_CONFIRM_TASK"]

ReceiveConfirmTask_Failed(i, msg, task) == 
    LET finished == Cardinality(Workers[i].unconfirmedTasks) = 1 
        firstTask == IF Cardinality(Workers[i].confirmedTasks) = 0 THEN NULL 
                     ELSE CHOOSE t \in Workers[i].confirmedTasks: \A y \in Workers[i].confirmedTasks: 
                                 t.taskId # y.taskId => t.taskId < y.taskId
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId},
                   ![i].confirmedTasks = IF finished THEN 
                                            IF Cardinality(Workers[i].confirmedTasks) > 0
                                            THEN Workers[i].confirmedTasks \ {firstTask}
                                            ELSE {} 
                                         ELSE Workers[i].confirmedTasks,               
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN
                                    IF Cardinality(Workers[i].confirmedTasks) > 0
                                    THEN "RECV_SEND_KEY"
                                    ELSE "SEND_QUERY_TASKS"
                                ELSE "SEND_CONFIRM_TASK"]
                                
ReceiveConfirmTask(i) == 
    /\ ReceiveConfirmTask_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, m)
       IN \/ /\ msg.type # "NOT_REGISTERED"
             /\ LET task == CHOOSE t \in Workers[i].unconfirmedTasks : msg.task = t.address
                IN \/ /\ msg.type = "CONFIRM_SUCCESS" 
                      /\ ReceiveConfirmTask_Success(i, msg, task)
                   \/ /\ msg.type # "CONFIRM_SUCCESS"
                      /\ ReceiveConfirmTask_Failed(i, msg, task)
          \/ /\ msg.type = "NOT_REGISTERED"
             /\ Terminate(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

(***************************************************************************)
(*                             RECV_SEND_KEY                               *)
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
    /\ Time < Workers[i].currentTask.Sd
    /\ \E msg \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, msg) 

ReceiveSendKey(i) == 
    /\ ReceiveSendKey_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, m)
           decryptedKeyshare == Decrypt(msg.keyshare, Workers[i].sk)
           response == [type |-> "ACK", 
                        from |-> Workers[i].pk,
                        task |-> Workers[i].currentTask.address]
       IN /\ SendMessage(msg.from, response)
          /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                        ![i].requesterSk = decryptedKeyshare, 
                                        ![i].state = "COMPUTE"] 
    /\ UNCHANGED <<TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                                COMPUTE                                  *)
(***************************************************************************)
Compute_IsEnabled(i) == 
    /\ Workers[i].state = "COMPUTE"
    /\ Workers[i].requesterSk # NULL 
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    
Compute(i) == 
    /\ Compute_IsEnabled(i) 
    /\ Workers' = [Workers EXCEPT ![i].state = "SEND_SUBMIT_DATA"] \* TODO
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                   SEND_SUBMIT_DATA / RECV_SUBMIT_DATA                   *)
(***************************************************************************)
SendSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_DATA" 
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd

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

ReceiveSubmitData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "hash"} : f \in DOMAIN msg
    /\ msg.type = "HASH" 
    /\ msg.from = Storage.pk

ReceiveSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_DATA" 
    /\ Workers[i].requesterSk # NULL 
    /\ Workers[i].currentHash = NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitData_MessageFormat(i, msg)

ReceiveSubmitData(i) == 
    /\ ReceiveSubmitData_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitData_MessageFormat(i, m) 
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                     ![i].state = "SEND_SUBMIT_HASH",
                                     ![i].currentHash = msg.hash]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                   SEND_SUBMIT_HASH / RECV_SUBMIT_HASH                   *)
(***************************************************************************)
SendSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_HASH"
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentHash # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd

SendSubmitHash(i) ==
    /\ SendSubmitHash_IsEnabled(i)
    /\ LET request == [type |-> "SUBMIT_HASH", 
                       from |-> Workers[i].pk,
                       hash |-> Workers[i].currentHash,
                       task |-> Workers[i].currentTask.address]
       IN /\ SendMessage(TSCs.pk, request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_HASH"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>

ReceiveSubmitHash_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg 
    /\ msg.from = TSCs.pk
    /\ msg.type \in {"ACK", "INVALID", "COMPLETED", "CANCELED", "NOT_REGISTERED"}
    /\ msg.type \in {"ACK", "INVALID", "COMPLETED", "CANCELED"} \equiv "task" \in DOMAIN msg

ReceiveSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_HASH" 
    /\ Workers[i].requesterSk # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, msg)

ReceiveSubmitHash(i) == 
    /\ ReceiveSubmitHash_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, m)
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                     ![i].state = "RECV_WEIGHTS"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                              RECV_WEIGHTS                               *)
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
    /\ Time < Workers[i].currentTask.Pd
    /\ \E msg \in Workers[i].msgs : ReceiveWeights_MessageFormat(i, msg) 
    
ReceiveWeights(i) == 
    /\ ReceiveWeights_IsEnabled(i) 
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveWeights_MessageFormat(i, m)
           otherParticipants == {w.address : w \in {weight \in msg.weights : 
                                 weight.address # Workers[i].pk}}
           response == [type |-> "ACK", 
                        from |-> Workers[i].pk,
                        task |-> Workers[i].currentTask.address] 
       IN /\ SendMessage(msg.from, response)
          /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg}, 
                                        ![i].requesterWeights = msg.weights,
                                        ![i].participantsSent = otherParticipants, 
                                        ![i].participantsRcvd = otherParticipants,
                                        ![i].state = "SEND_QUERY_DATA"]
    /\ UNCHANGED <<TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                    SEND_QUERY_DATA / RECV_QUERY_DATA                    *)
(***************************************************************************)
SendQueryData_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_QUERY_DATA"
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Pd

SendQueryData(i) == 
    /\ SendQueryData_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_DATA", 
                       from |-> Workers[i].pk, 
                     hashes |-> {Workers[i].currentHash}]
       IN /\ SendMessage(Storage.pk, request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Requesters, TSCs, USCs>> 
    
ReceiveQueryData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "allData"} : f \in DOMAIN msg
    /\ msg.from = Storage.pk
    /\ msg.type = "DATA"

ReceiveQueryData_IsEnabled(i) ==
    /\ Workers[i].state = "RECV_QUERY_DATA"
    /\ Workers[i].currentTask # NULL
    /\ \E msg \in Workers[i].msgs : ReceiveQueryData_MessageFormat(i, msg)
    /\ Time < Workers[i].currentTask.Pd

ReceiveQueryData(i) == 
    /\ ReceiveQueryData_IsEnabled(i)
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
    
(***************************************************************************)
(*                 REQUEST_DATA / RECEIVE_DATA/ SEND_DATA                  *)
(***************************************************************************)
RequestData_IsEnabled(i) == 
    /\ Workers[i].state = "REQUEST_DATA"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].submittedData # {}
    /\ Workers[i].participantsSent # {}
    /\ Time < Workers[i].currentTask.Pd
    
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

ReceiveData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task", "data"} : f \in DOMAIN msg
    /\ msg.from \in Workers[i].participantsSent
    /\ msg.type = "DATA"
    /\ msg.task = Workers[i].currentTask.address

ReceiveData_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_DATA"
    /\ Workers[i].currentTask # NULL 
    /\ \E msg \in Workers[i].msgs : ReceiveData_MessageFormat(i, msg)
    /\ Time < Workers[i].currentTask.Pd

ReceiveData(i) == 
    /\ ReceiveData_IsEnabled(i)
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
    
SendData_MessageFormat(i, msg) == 
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from \in Workers[i].participantsRcvd
    /\ msg.type = "GET_DATA"
    /\ msg.task = Workers[i].currentTask.address
    
SendData_IsEnabled(i) == 
    /\ Workers[i].state \in {"REQUEST_DATA", "RECV_DATA"} 
    /\ Workers[i].currentTask # NULL 
    /\ \E msg \in Workers[i].msgs : SendData_MessageFormat(i, msg)
    /\ Time < Workers[i].currentTask.Pd
    
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
(***************************************************************************)
Verify_IsEnabled(i) == 
    /\ Workers[i].state = "VERIFY"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].requesterSk # NULL
    /\ Time < Workers[i].currentTask.Pd

Verify(i) == 
    /\ Verify_IsEnabled(i)
    /\ LET weights == CATDAlgorithm(i)
       IN Workers' = [Workers EXCEPT ![i].weights = weights, 
                                     ![i].state = "SEND_SUBMIT_EVAL"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                   SEND_SUBMIT_EVAL / RECV_SUBMIT_EVAL                   *)
(***************************************************************************)
SendSubmitEval_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_EVAL"
    /\ Workers[i].currentTask # NULL 
    /\ Workers[i].weights # NULL
    /\ Time < Workers[i].currentTask.Pd

SendSubmitEval(i) == 
    /\ SendSubmitEval_IsEnabled(i) 
    /\ LET request == [type |-> "SUBMIT_EVAL",
                       from |-> Workers[i].pk,
                       task |-> Workers[i].currentTask.address,
                    weights |-> Workers[i].weights]
       IN /\ SendMessage(TSCs.pk, request) 
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_EVAL"]
    /\ UNCHANGED <<Requesters, USCs, Storage>> 

ReceiveSubmitEval_MessageFormat(i, msg) ==
    /\ \A f \in {"from", "type", "task"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type = "ACK"

ReceiveSubmitEval_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_EVAL" 
    /\ Workers[i].currentTask # NULL
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitEval_MessageFormat(i, msg)
    /\ Time < Workers[i].currentTask.Pd 
    
ReceiveSubmitEval(i) ==
    /\ ReceiveSubmitEval_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitEval_MessageFormat(i, m)
       IN NextTask(i, msg)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
(***************************************************************************)
(*                     AUTOMATIC TIMEOUTS & TERMINATION                    *)
(***************************************************************************)
EarlyTermination_IsEnabled(i) == 
    /\ Time >= TaskQueryDeadline
    /\ Workers[i].state \in {"INIT", 
                             "SEND_REGISTER", 
                             "RECV_REGISTER",
                             "SEND_QUERY_TASKS", 
                             "RECV_QUERY_TASKS"}
                             
EarlyTermination(i) == 
    /\ EarlyTermination_IsEnabled(i) 
    /\ Terminate(i, NULL)
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

TaskTimeout_IsEnabled(i) == 
    /\ Workers[i].currentTask # NULL
    /\ \/ /\ Time >= Workers[i].currentTask.Sd          \* Case 1: Submission not complete before Submission deadline
          /\ Workers[i].state \in {"RECV_SEND_KEY", 
                                   "COMPUTE",
                                   "SEND_SUBMIT_DATA", 
                                   "RECV_SUBMIT_DATA", 
                                   "SEND_SUBMIT_HASH", 
                                   "RECV_SUBMIT_HASH"}  
       \/ /\ Time >= Workers[i].currentTask.Pd          \* Case 2: Evaluation not complete before Proving deadline
          /\ Workers[i].state \in {"RECV_WEIGHTS",
                                   "SEND_QUERY_HASHES", 
                                   "RECV_QUERY_HASHES",
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
    
Terminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage>> 
        
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
        \/ ReceiveQueryTasks(worker)
        \/ ReceiveConfirmTask(worker)
        \/ ReceiveSendKey(worker)
        \/ ReceiveSubmitData(worker)
        \/ ReceiveSubmitHash(worker)
        \/ ReceiveWeights(worker)
        \/ ReceiveQueryData(worker)
        \/ ReceiveData(worker)
        \/ ReceiveSubmitEval(worker)
        \/ EarlyTermination(worker)
        \/ TaskTimeout(worker)
    \/ Terminating
        
=============================================================================
\* Modification History
\* Last modified Fri Mar 01 15:07:54 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
