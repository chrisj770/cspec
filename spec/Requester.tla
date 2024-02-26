----------------------------- MODULE Requester -----------------------------
EXTENDS FiniteSets, Sequences, Common

CONSTANT Tasks

RequiredTaskFields == {
    "id",               \* Unique identifier (starting at 1..)
    "Sd",               \* Submission deadline (time in steps)
    "Pd",               \* Proving deadline (time, in steps)
    "Td",               \* Task deadline (time, in steps)
    "numParticipants"}  \* Required number of participants

ASSUME /\ \A d \in RequiredTaskFields : d \in DOMAIN Tasks
       /\ \A t \in Tasks: /\ t.Td >= t.Pd
                          /\ t.Pd >= t.Sd
       /\ \A t \in Tasks: ~(\E u \in Tasks : t.id = u.id)
        
TypeOK == 
    /\ \A requester \in Requesters : [requester.state ->
        {"INIT",                \* Initialize local variables
         "SEND_REGISTER",       \* Attempt to register as a REQUESTER via USSC
         "RECV_REGISTER",       \* Receive acknowledgement and public/private key from USSC
         "SEND_POST_TASKS",     \* Attempt to post a list of tasks via TSSC
         "RECV_POST_TASKS",     \* Receive acknowledgement for task post from TSSC
         "SEND_QUERY_TASKS",    \* Request a list of active tasks via TSC
         "RECV_QUERY_TASKS",    \* Receive a list of active tasks from TSC, or INVALID
         "SEND_KEY",            \* Attempt to send key-share to WORKER for single task
         "RECV_KEY",            \* Receive acknowledgement for key-share from WORKER 
         "SEND_QUERY_HASHES",   \* Request list of all hashes from TSC
         "RECV_QUERY_HASHES",   \* Receive list of all hashes from TSC
         "SEND_QUERY_DATA",     \* Request all relevant sensory data from STORAGE
         "RECV_QUERY_DATA",     \* Receive all relevant sensory data from STORAGE
         "EVALUATE",            \* Run evaluation process
         "SEND_SUBMIT_EVAL",    \* Attempt to submit results of evaluation via TSC
         "RECV_SUBMIT_EVAL",    \* Receive acknowledgement for evaluation results from TSC
         "SEND_WEIGHTS",        \* Attempt to broadcast weights received from evaluation
         "TERMINATED"}]  

Init == 
    Requesters = [r \in 1..NumRequesters |-> [
                    msgs |-> {}, 
                    state |-> "SEND_REGISTER",
                    pubkey |-> "",
                    tasks |-> Tasks,
                    currentTask |-> NULL,
                    unconfirmedWorkers |-> {}, 
                    confirmedWorkers |-> {},
                    hashes |-> {},
                    data |-> {}]]

SendRegister_IsEnabled(i) ==
    /\ Requesters[i].state = "SEND_REGISTER"
            
SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                      userType |-> "REQUESTER", 
                      src |-> i]
       IN /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, USCs, TSCs, Storage>>

ReceiveRegister_MessageFormat(i, msg) == 
    /\ msg.src = "USSC"
    /\ msg.type \in {"REGISTERED", "NOT_REGISTERED"}

ReceiveRegister_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_REGISTER"
    /\ \E msg \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, msg)
    
ReceiveRegister(i) == 
    /\ ReceiveRegister_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveRegister_MessageFormat(i, m)
       IN Requesters' = [Requesters EXCEPT ![i].pubkey = IF msg.type = "REGISTERED"
                                                         THEN msg.pubkey 
                                                         ELSE Requesters[i].pubkey,
                                           ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].state = IF msg.type = "REGISTERED"
                                                        THEN "SEND_POST_TASKS"
                                                        ELSE "TERMINATED"]
    /\ UNCHANGED <<Workers, USSC, USCs, TSCs, Storage>>
    
SendPostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    
SendPostTasks(i) == 
    /\ SendPostTasks_IsEnabled(i) 
    /\ LET request == [type |-> "POST_TASKS", 
                      pubkey |-> Requesters[i].pubkey, 
                      tasks |-> Requesters[i].tasks]
       IN /\ SendMessage("TSC", request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, USSC, USCs, Storage>>

ReceivePostTasks_MessageFormat(i, msg) == 
    /\ msg.pubkey = "TSC"
    /\ msg.type \in {"ACK", "INVALID"}

ReceivePostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_POST_TASKS"
    /\ \E msg \in Requesters[i].msgs: ReceivePostTasks_MessageFormat(i, msg)
    
ReceivePostTasks(i) == 
    /\ ReceivePostTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceivePostTasks_MessageFormat(i, m) 
       IN Requesters' = [Requesters EXCEPT ![i].tasks = IF msg.type # "ACK" THEN {}
                                                        ELSE Requesters[i].tasks,
                                           ![i].state = IF msg.type = "ACK" 
                                                        THEN "SEND_QUERY_TASKS"
                                                        ELSE "TERMINATED",
                                           ![i].msgs = Requesters[i].msgs \ {msg}]
    /\ UNCHANGED <<Workers, USSC, USCs, TSCs, Storage>>
    
SendQueryTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_TASKS"
    
SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                      pubkey |-> Requesters[i].pubkey, 
                      owner |-> Requesters[i].pubkey]
       IN /\ SendMessage("TSC", request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, USSC, USCs, Storage>>
     
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ msg.pubkey = "TSC" 
    /\ msg.type \in {"TASKS", "INVALID"}

ReceiveQueryTasks_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Requesters[i].msgs: ReceiveQueryTasks_MessageFormat(i, msg)
    
ReceiveQueryTasks_Success(i, msg) == 
    IF Cardinality(msg.tasks) = 0 
    THEN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                          ![i].tasks = msg.tasks,
                                          ![i].state = "TERMINATED"]
    ELSE LET firstTask == CHOOSE t \in msg.tasks : \A y \in msg.tasks : 
                          t.taskId # y.taskId => t.taskId < y.taskId 
         IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                             ![i].tasks = msg.tasks \ {firstTask},
                                             ![i].unconfirmedWorkers = firstTask.participants, 
                                             ![i].confirmedWorkers = {},
                                             ![i].currentTask = firstTask,
                                             ![i].state = "SEND_KEY"]
     
ReceiveQueryTasks(i) == 
    /\ ReceiveQueryTasks_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryTasks_MessageFormat(i, m) 
       IN IF msg.type = "TASKS"
          THEN ReceiveQueryTasks_Success(i, msg)
          ELSE Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>

SendKey_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_KEY"
    /\ Requesters[i].currentTask # NULL
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ Time < Requesters[i].currentTask.Sd

SendKey(i) ==
    /\ SendKey_IsEnabled(i)
    /\ LET nextWorkerPubkey == CHOOSE r \in Requesters[i].unconfirmedWorkers : TRUE 
           request == [type |-> "SEND_KEY", 
                      pubkey |-> Requesters[i].pubkey, 
                      keyshare |-> "PlaceholderKeyshare"]
       IN /\ SendMessage(nextWorkerPubkey, request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_KEY"]
    /\ UNCHANGED <<TSCs, USSC, USCs, Storage>>

ReceiveKey_MessageFormat(i, msg) == 
    /\ msg.type = "ACK" 
    /\ msg.pubkey \in Requesters[i].unconfirmedWorkers

ReceiveKey_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_KEY"
    /\ Requesters[i].currentTask # NULL    
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ \E msg \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, msg)
    /\ Time < Requesters[i].currentTask.Sd
    
ReceiveKey(i) == 
    /\ ReceiveKey_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, m) 
           worker == CHOOSE w \in Requesters[i].unconfirmedWorkers : w = msg.pubkey 
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].unconfirmedWorkers = Requesters[i].unconfirmedWorkers \ {worker},
                                           ![i].confirmedWorkers = Requesters[i].confirmedWorkers \union {worker},
                                           ![i].state = IF Cardinality(Requesters[i].confirmedWorkers) + 1 = Cardinality(Requesters[i].currentTask.participants)
                                                        THEN "SEND_QUERY_HASHES"
                                                        ELSE "SEND_KEY"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>

SendQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_HASHES"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ Time < Requesters[i].currentTask.Pd

SendQueryHashes(i) == 
    /\ SendQueryHashes_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_HASHES", 
                      pubkey |-> Requesters[i].pubkey, 
                      task |-> Requesters[i].currentTask.pubkey] 
       IN /\ SendMessage("TSC", request)
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_HASHES"]
    /\ UNCHANGED <<Workers, USSC, USCs, Storage>>
    
ReceiveQueryHashes_MessageFormat(i, msg) == 
    /\ msg.pubkey = "TSC"
    /\ msg.type = "HASHES" 
    /\ msg.task = Requesters[i].currentTask.pubkey
    /\ "hashes" \in DOMAIN msg

ReceiveQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_QUERY_HASHES"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, msg)
    /\ Time < Requesters[i].currentTask.Pd

ReceiveQueryHashes(i) == 
    /\ ReceiveQueryHashes_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, m)
       IN /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                              ![i].state = "SEND_QUERY_DATA", 
                                              ![i].hashes = msg.hashes]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>

SendQueryData_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_DATA"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ Time < Requesters[i].currentTask.Pd

SendQueryData(i) == 
    /\ SendQueryData_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_DATA", 
                      pubkey |-> Requesters[i].pubkey, 
                      hashes |-> Requesters[i].hashes]
       IN /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs>> 
    
ReceiveQueryData_MessageFormat(i, msg) == 
    /\ msg.type = "DATA"
    /\ msg.src = "STORAGE"
    /\ "data" \in DOMAIN msg

ReceiveQueryData_IsEnabled(i) ==
    /\ Requesters[i].state = "RECV_QUERY_DATA"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, msg)
    /\ Time < Requesters[i].currentTask.Pd

ReceiveQueryData(i) == 
    /\ ReceiveQueryData_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryData_MessageFormat(i, m)
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                           ![i].data = msg.data,
                                           ![i].state = "EVALUATE"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>
    
Evaluate_IsEnabled(i) == 
    /\ Requesters[i].state = "EVALUATE"
    /\ Requesters[i].currentTask # NULL
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ Cardinality(Requesters[i].data) = Requesters[i].currentTask.numParticipants
    /\ Time < Requesters[i].currentTask.Pd
 
Evaluate(i) ==
    /\ Evaluate_IsEnabled(i) 
    /\ Requesters' = [Requesters EXCEPT ![i].state = "SUBMIT_EVAL"] \* TODO 
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>
    
GetLastTaskDeadline(r) ==
    LET lastTask == CHOOSE t \in r.tasks : \A y \in r.tasks : t.Td # y.Td => t.Td >= y.Td IN lastTask.Td
    
EarlyTermination_IsEnabled(i) == 
    \/ /\ Requesters[i].state = "SEND_REGISTER"      \* Case 1: No tasks to submit prior to registration     
       /\ Cardinality(Requesters[i].tasks) = 0 
    \/ /\ Cardinality(Requesters[i].tasks) > 0
       /\ Time >= GetLastTaskDeadline(Requesters[i]) \* Case 2: Registration/Post not finished before final Task deadline
       /\ Requesters[i].state \in {"RECV_REGISTER",  
                                   "RECV_POST_TASKS", 
                                   "RECV_QUERY_TASKS"}
                            
EarlyTermination(i) == 
    /\ EarlyTermination_IsEnabled(i) 
    /\ Requesters' = [Requesters EXCEPT ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>> 
        
TaskTimeout_IsEnabled(i) == 
    /\ Requesters[i].currentTask # NULL
    /\ \/ /\ Time >= Requesters[i].currentTask.Sd   \* Case 1: Keys not sent/ACKed before Submission deadline
          /\ Requesters[i].state \in {"SEND_KEY", 
                                      "RECV_KEY"}  
       \/ /\ Time >= Requesters[i].currentTask.Pd   \* Case 2: Evaluation not complete before Proving deadline
          /\ Requesters[i].state \in {"SEND_QUERY_HASHES",  
                                      "RECV_QUERY_HASHES",
                                      "SEND_QUERY_DATA",
                                      "RECV_QUERY_DATA",
                                      "EVALUATE",
                                      "SEND_SUBMIT_EVAL",
                                      "RECV_SUBMIT_EVAL",
                                      "SEND_WEIGHTS"}

TaskTimeout(i) == 
    /\ TaskTimeout_IsEnabled(i) 
    /\ LET r == Requesters[i]
           nextTask == IF Cardinality(Requesters[i].tasks) = 0 THEN NULL ELSE 
                       CHOOSE t \in r.tasks : \A y \in r.tasks : 
                              t.taskId # y.taskId => t.taskId < y.taskId   
       IN Requesters' = [Requesters EXCEPT 
           ![i].state = IF nextTask = NULL THEN "TERMINATED" ELSE "SEND_KEY",
           ![i].tasks = IF nextTask = NULL THEN r.tasks ELSE r.tasks \ {nextTask},
           ![i].currentTask = nextTask,
           ![i].unconfirmedWorkers = IF nextTask = NULL THEN {} ELSE nextTask.participants,
           ![i].confirmedWorkers = {}, 
           ![i].hashes = {},
           ![i].data = {}]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>
    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSCs, USSC, USCs, Storage>> 

Terminated == 
    <>(\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")
            
Next == 
    \/ \E requester \in 1..NumRequesters : 
        \/ SendRegister(requester)
        \/ SendPostTasks(requester)
        \/ SendQueryTasks(requester)
        \/ SendKey(requester)
        \/ SendQueryHashes(requester)
        \/ SendQueryData(requester)
        \/ Evaluate(requester)
        \/ ReceiveRegister(requester)        
        \/ ReceivePostTasks(requester)
        \/ ReceiveQueryTasks(requester)
        \/ ReceiveKey(requester)
        \/ ReceiveQueryHashes(requester)
        \/ ReceiveQueryData(requester)
        \/ EarlyTermination(requester)
        \/ TaskTimeout(requester)
    \/ Terminating
    
=============================================================================
\* Modification History
\* Last modified Mon Feb 26 08:43:25 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
