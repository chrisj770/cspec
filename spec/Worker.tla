------------------------------- MODULE Worker -------------------------------
EXTENDS FiniteSets, Sequences, Common, TLC, Integers
    
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
         "SEND_SUBMIT_EVAL",    \* Attempt to submit evaluation results to TSC  
         "RECV_SUBMIT_EVAL",    \* Receive Acknowledgement for evaluation results from TSC
         "TERMINATED"}]         
         
StateConsistency == TRUE
         
Init ==
    Workers = [w \in 1..NumWorkers |-> [
                msgs |-> {}, 
                state |-> "SEND_REGISTER",
                address |-> "",
                unconfirmedTasks |-> {}, 
                confirmedTasks |-> {}, 
                currentTask |-> NULL,
                keyshare |-> NULL, 
                currentHash |-> NULL]]

SendRegister_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_REGISTER"

SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                      userType |-> "WORKER", 
                      src |-> i]
       IN /\ SendMessage("USC", request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Requesters, TSCs, Storage>>

ReceiveRegister_MessageFormat(i, msg) == 
    /\ msg.address = "USC"
    /\ \/ msg.type = "NOT_REGISTERED"
       \/ /\ msg.type = "REGISTERED"
          /\ "key" \in DOMAIN msg

ReceiveRegister_IsEnabled(i) ==
    /\ Workers[i].state = "RECV_REGISTER"
    /\ \E msg \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, msg)

ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveRegister_MessageFormat(i, m)
       IN Workers' = [Workers EXCEPT ![i].address = IF msg.type = "REGISTERED" 
                                                   THEN msg.key
                                                   ELSE Workers[i].address,
                                     ![i].msgs = Workers[i].msgs \ {msg}, 
                                     ![i].state = IF msg.type = "REGISTERED" 
                                                  THEN "SEND_QUERY_TASKS"
                                                  ELSE "TERMINATED"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

SendQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_QUERY_TASKS"

SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                      address |-> Workers[i].address,
                      owner |-> NULL]
       IN /\ SendMessage("TSC", request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>
    
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ msg.address = "TSC"
    /\ msg.type \in {"TASKS", "INVALID"}

ReceiveQueryTasks_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, msg)
    
ReceiveQueryTasks_Success(i, msg) == 
    Workers' = [Workers EXCEPT 
                ![i].msgs = Workers[i].msgs \ {msg},
                ![i].unconfirmedTasks = msg.tasks,
                ![i].state = IF Cardinality(msg.tasks) > 0
                             THEN "SEND_CONFIRM_TASK"
                             ELSE "TERMINATED"]
    
ReceiveQueryTasks(i) ==
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveQueryTasks_MessageFormat(i, m)
       IN IF msg.type = "TASKS" 
          THEN ReceiveQueryTasks_Success(i, msg)
          ELSE Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                          ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

SendConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_CONFIRM_TASK" 

SendConfirmTask(i) == 
    /\ SendConfirmTask_IsEnabled(i)
    /\ LET currTask == CHOOSE tsc \in Workers[i].unconfirmedTasks :
                       \A other \in Workers[i].unconfirmedTasks: 
                       tsc # other => tsc.taskId < other.taskId
           request == [type |-> "CONFIRM_TASK", 
                      address |-> Workers[i].address, 
                      task |-> currTask.address]
       IN /\ SendMessage("TSC", request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_CONFIRM_TASK"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>

ReceiveConfirmTask_MessageFormat(i, msg) == 
    /\ msg.address = "TSC"
    /\ \/ msg.type \in {"INVALID", "CANCELED", "COMPLETED", "NOT_REGISTERED"}
       \/ /\ msg.type \in {"CONFIRM_FAIL", "CONFIRM_SUCCESS"}
          /\ msg.task \in {t.address : t \in Workers[i].unconfirmedTasks}

ReceiveConfirmTask_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_CONFIRM_TASK"
    /\ \E msg \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, msg)
    
ReceiveConfirmTask_Success(i, msg, task) == 
    LET newTasks == Workers[i].confirmedTasks \union {task} 
        firstTask == CHOOSE t \in newTasks: \A y \in newTasks: 
                            t.taskId # y.taskId => t.taskId < y.taskId
        finished == Cardinality(Workers[i].unconfirmedTasks) = 1 
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId}, 
                   ![i].confirmedTasks = newTasks,
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN "RECV_SEND_KEY" ELSE "SEND_CONFIRM_TASK"]

ReceiveConfirmTask_Failed(i, msg, task) == 
    LET newTasks == Workers[i].confirmedTasks
        firstTask == IF Cardinality(newTasks) = 0 THEN NULL 
                     ELSE CHOOSE t \in newTasks: \A y \in newTasks: 
                                 t.taskId # y.taskId => t.taskId < y.taskId
        finished == Cardinality(Workers[i].unconfirmedTasks) = 1 
    IN Workers' = [Workers EXCEPT 
                   ![i].msgs = Workers[i].msgs \ {msg},
                   ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId},
                   ![i].currentTask = IF finished THEN firstTask ELSE NULL,
                   ![i].state = IF finished THEN
                                    IF Cardinality(Workers[i].confirmedTasks) > 0
                                    THEN "RECV_SEND_KEY"
                                    ELSE "SEND_QUERY_TASK"
                                ELSE "SEND_CONFIRM_TASK"]

ReceiveConfirmTask(i) == 
    /\ ReceiveConfirmTask_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveConfirmTask_MessageFormat(i, m)
       IN IF msg.type \in {"CONFIRM_SUCCESS", "CONFIRM_FAILED"}
          THEN LET task == CHOOSE t \in Workers[i].unconfirmedTasks : msg.task = t.address
               IN IF msg.type = "CONFIRM_SUCCESS" 
                  THEN ReceiveConfirmTask_Success(i, msg, task)
                  ELSE ReceiveConfirmTask_Failed(i, msg, task)
          ELSE Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg}]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

ReceiveSendKey_MessageFormat(i, msg) == 
    /\ msg.type = "SEND_KEY" 
    /\ msg.address = Workers[i].currentTask.owner

ReceiveSendKey_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SEND_KEY"
    /\ Workers[i].keyshare = NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    /\ \E msg \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, msg) 

ReceiveSendKey(i) == 
    /\ ReceiveSendKey_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSendKey_MessageFormat(i, m)
           rid == CHOOSE r \in 1..NumRequesters : Requesters[r].address = msg.address
           response == [type |-> "ACK", address |-> Workers[i].address]
       IN /\ SendMessage(msg.address, response)
          /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                        ![i].keyshare = msg.keyshare, 
                                        ![i].state = "COMPUTE"] 
    /\ UNCHANGED <<TSCs, USCs, Storage>>

Compute_IsEnabled(i) == 
    /\ Workers[i].state = "COMPUTE"
    /\ Workers[i].keyshare # NULL 
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    
Compute(i) == 
    /\ Compute_IsEnabled(i) 
    /\ Workers' = [Workers EXCEPT ![i].state = "SEND_SUBMIT_DATA"] \* TODO
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>

SendSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_DATA" 
    /\ Workers[i].keyshare # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd

SendSubmitData(i) == 
    /\ SendSubmitData_IsEnabled(i) 
    /\ LET request == [type |-> "SUBMIT_DATA", 
                      address |-> Workers[i].address, 
                      data |-> "DataPlaceholder"]
       IN /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {request}]
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_DATA"]
    /\ UNCHANGED <<Requesters, TSCs, USCs>>

ReceiveSubmitData_MessageFormat(i, msg) == 
    /\ msg.type = "HASH" 
    /\ msg.address = "STORAGE"

ReceiveSubmitData_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_DATA" 
    /\ Workers[i].keyshare # NULL 
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

SendSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "SEND_SUBMIT_HASH"
    /\ Workers[i].keyshare # NULL
    /\ Workers[i].currentHash # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd

SendSubmitHash(i) ==
    /\ SendSubmitHash_IsEnabled(i)
    /\ LET request == [type |-> "SUBMIT_HASH", 
                      address |-> Workers[i].address,
                      hash |-> Workers[i].currentHash,
                      task |-> Workers[i].currentTask.address]
       IN /\ SendMessage("TSC", request)
          /\ Workers' = [Workers EXCEPT ![i].state = "RECV_SUBMIT_HASH"]
    /\ UNCHANGED <<Requesters, USCs, Storage>>

ReceiveSubmitHash_MessageFormat(i, msg) == 
    /\ msg.type = "ACK" 
    /\ msg.task = Workers[i].currentTask.address
    /\ msg.address = "TSC"

ReceiveSubmitHash_IsEnabled(i) == 
    /\ Workers[i].state = "RECV_SUBMIT_HASH" 
    /\ Workers[i].keyshare # NULL
    /\ Workers[i].currentTask # NULL
    /\ Time < Workers[i].currentTask.Sd
    /\ \E msg \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, msg)

ReceiveSubmitHash(i) == 
    /\ ReceiveSubmitHash_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Workers[i].msgs : ReceiveSubmitHash_MessageFormat(i, m)
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                     ![i].state = "RECV_WEIGHTS"]
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
                                   "SEND_SUBMIT_EVAL",
                                   "RECV_SUBMIT_EVAL"}
    
TaskTimeout(i) == 
    /\ TaskTimeout_IsEnabled(i) 
    /\ LET newTasks == Workers[i].confirmedTasks \ Workers[i].currentTask 
           nextTask == IF Cardinality(newTasks) = 0 THEN NULL ELSE 
                       CHOOSE t \in newTasks : \A y \in newTasks : 
                              t.taskId # y.taskId => t.taskId < y.taskId   
       IN Workers' = [Workers EXCEPT 
           ![i].state = IF nextTask = NULL THEN "SEND_QUERY_TASKS" ELSE "GET_KEY",
           ![i].currentTask = nextTask,
           ![i].confirmedTasks = newTasks,
           ![i].keyshare = NULL, 
           ![i].currentHash = NULL]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage>>
    
Terminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage>> 

Terminated == <>(\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")
        
Next == 
    \/ \E worker \in 1..NumWorkers : 
        \/ SendRegister(worker)
        \/ SendQueryTasks(worker)
        \/ SendConfirmTask(worker) 
        \/ SendSubmitData(worker) 
        \/ SendSubmitHash(worker)
        \/ Compute(worker)      
        \/ ReceiveRegister(worker)
        \/ ReceiveQueryTasks(worker)
        \/ ReceiveConfirmTask(worker)
        \/ ReceiveSendKey(worker)
        \/ ReceiveSubmitData(worker)
        \/ ReceiveSubmitHash(worker)
        \/ TaskTimeout(worker)
    \/ Terminating
        
=============================================================================
\* Modification History
\* Last modified Mon Feb 26 11:05:48 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
