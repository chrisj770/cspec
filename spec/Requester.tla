----------------------------- MODULE Requester -----------------------------
EXTENDS FiniteSets, Sequences, Common

CONSTANT Tasks
        
TypeOK == 
    /\ \A requester \in Requesters : [requester.state ->
        {"INIT",                \* Initialize local variables
         "SEND_REGISTER",       \* Attempt to register as a REQUESTER via USSC
         "RECV_REGISTER",       \* Receive acknowledgement and public/private key from USSC
         "SEND_POST_TASKS",     \* Attempt to post a list of tasks via TSSC
         "RECV_POST_TASKS",     \* Receive acknowledgement for task post from TSSC
         "SEND_QUERY_TASKS",    \* Request a list of active tasks via TSSC
         "RECV_QUERY_TASKS",    \* Receive a list of active tasks from TSSC, or INVALID
         "SEND_KEY",            \* Attempt to send key-share to WORKER for single task
         "RECV_KEY",            \* Receive acknowledgement for key-share
         "SEND_QUERY_HASHES",   \* Request list of all hashes from TSC
         "RECV_QUERY_HASHES",   \* Receive list of all hashes from TSC
         "QUERY_DATA",          \* Request all relevant sensory data from STORAGE
         "EVALUATE",            \* Run evaluation process
         "SUBMIT_EVAL",         \* Attempt to submit results of evaluation via TSC
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
                    unconfirmedHashes |-> {},
                    confirmedHashes |-> {}]]

SendRegister_IsEnabled(i) ==
    /\ Requesters[i].state = "SEND_REGISTER"
            
SendRegister(i) == 
    /\ SendRegister_IsEnabled(i)
    /\ LET request == [type |-> "REGISTER", 
                      userType |-> "REQUESTER", 
                      src |-> i]
       IN /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, USCs, TSSC, TSCs, Storage>>

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
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs, Storage>>
    
SendPostTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    
SendPostTasks(i) == 
    /\ SendPostTasks_IsEnabled(i) 
    /\ LET request == [type |-> "POST_TASKS", 
                      pubkey |-> Requesters[i].pubkey, 
                      tasks |-> Requesters[i].tasks]
       IN /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>

ReceivePostTasks_MessageFormat(i, msg) == 
    /\ msg.src = "TSSC"
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
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs, Storage>>
    
SendQueryTasks_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_TASKS"
    
SendQueryTasks(i) == 
    /\ SendQueryTasks_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_TASKS", 
                      pubkey |-> Requesters[i].pubkey, 
                      owner |-> Requesters[i].pubkey]
       IN /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs, Storage>>
     
ReceiveQueryTasks_MessageFormat(i, msg) == 
    /\ msg.src = "TSSC" 
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
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs, Storage>>

SendKey_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_KEY"
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0

SendKey(i) ==
    /\ SendKey_IsEnabled(i)
    /\ LET nextWorkerPubkey == CHOOSE r \in Requesters[i].unconfirmedWorkers : TRUE 
           wid == CHOOSE w \in 1..NumWorkers : Workers[w].pubkey = nextWorkerPubkey
           request == [type |-> "SEND_KEY", 
                      pubkey |-> Requesters[i].pubkey, 
                      keyshare |-> "PlaceholderKeyshare"]
       IN /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_KEY"]
    /\ UNCHANGED <<TSSC, TSCs, USSC, USCs, Storage>>

ReceiveKey_MessageFormat(i, msg) == 
    /\ msg.type = "ACK" 
    /\ msg.pubkey \in Requesters[i].unconfirmedWorkers

ReceiveKey_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_KEY"
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ \E msg \in Requesters[i].msgs : ReceiveKey_MessageFormat(i, msg)
    
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
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs, Storage>>

SendQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_HASHES"
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers

SendQueryHashes(i) == 
    /\ SendQueryHashes_IsEnabled(i)
    /\ LET tsc == CHOOSE t \in TSCs : t.pubkey = Requesters[i].currentTask.pubkey
           request == [type |-> "QUERY_HASHES", pubkey |-> Requesters[i].pubkey] 
       IN /\ TSCs' = {IF t.taskId = Requesters[i].currentTask.taskId 
                      THEN [t EXCEPT !.msgs = t.msgs \union {request}]
                      ELSE t : t \in TSCs} 
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_HASHES"]
    /\ UNCHANGED <<Workers, TSSC, USSC, USCs, Storage>>
    
ReceiveQueryHashes_MessageFormat(i, msg) == 
    /\ msg.type = "HASHES" 
    /\ msg.pubkey = Requesters[i].currentTask.pubkey

ReceiveQueryHashes_IsEnabled(i) == 
    /\ Requesters[i].state = "RECV_QUERY_HASHES"
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ \E msg \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, msg)

ReceiveQueryHashes(i) == 
    /\ ReceiveQueryHashes_IsEnabled(i)
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : ReceiveQueryHashes_MessageFormat(i, m)
       IN /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                              ![i].state = "SEND_QUERY_DATA", 
                                              ![i].unconfirmedHashes = msg.hashes,
                                              ![i].confirmedHashes = {}]
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs, Storage>>


SendQueryData_IsEnabled(i) == 
    /\ Requesters[i].state = "SEND_QUERY_DATA"
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers

SendQueryData(i) == 
    /\ SendQueryData_IsEnabled(i)
    /\ LET request == [type |-> "QUERY_DATA", 
                      pubkey |-> Requesters[i].pubkey, 
                      hashes |-> Requesters[i].unconfirmedHashes]
       IN /\ Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {request}]
          /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_DATA"]
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs>> 
    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs, Storage>> 

Terminated == 
    <>(\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")
    
    
GetLastDeadline(r) ==
    LET lastTask == CHOOSE t \in r.tasks : \A y \in r.tasks : t.Sd # y.Sd => t.Sd >= y.Sd
    IN lastTask.Sd
                            
EarlyStopping(i) == 
    LET r == Requesters[i] IN
        IF \/ /\ r.state = "SEND_REGISTER"          \* Case 1: No tasks prior to registration     
              /\ Cardinality(r.tasks) = 0 
           \/ /\ r.state \in {"RECV_REGISTER",      \* Case 2: Registration/Post hangs before final task deadline
                              "RECV_POST_TASKS", 
                              "RECV_QUERY_TASKS"}
              /\ Time >= GetLastDeadline(r)
        THEN Requesters' = [Requesters EXCEPT ![i].state = "TERMINATED"]
        ELSE FALSE
            
Next == 
    \/ \E requester \in 1..NumRequesters : 
        \/ SendRegister(requester)
        \/ SendPostTasks(requester)
        \/ SendQueryTasks(requester)
        \/ SendKey(requester)
        \/ SendQueryHashes(requester)
        \/ SendQueryData(requester)
        \/ ReceiveRegister(requester)        
        \/ ReceivePostTasks(requester)
        \/ ReceiveQueryTasks(requester)
        \/ ReceiveKey(requester)
        \/ ReceiveQueryHashes(requester)
        \/ EarlyStopping(requester)
    \/ Terminating
    


=============================================================================
\* Modification History
\* Last modified Sun Feb 25 15:30:55 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
