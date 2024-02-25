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
                    confirmedWorkers |-> {}]]
                    
SendRegister(i) == 
    /\ Requesters[i].state = "SEND_REGISTER"
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \union 
        {[type |-> "REGISTER", 
          userType |-> "REQUESTER", 
          src |-> i]}]
    /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, USCs, TSSC, TSCs>>
    
ReceiveRegister(i) == 
    /\ Requesters[i].state = "RECV_REGISTER"
    /\ \E msg \in Requesters[i].msgs : msg.src = "USSC"
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : m.src = "USSC" IN
       \/ /\ msg.type = "REGISTERED"
          /\ Requesters' = [Requesters EXCEPT 
                           ![i].pubkey = msg.pubkey, 
                           ![i].msgs = Requesters[i].msgs \ {msg},
                           ![i].state = "SEND_POST_TASKS"]
       \/ /\ msg.type = "NOT_REGISTERED"
          /\ Requesters' = [Requesters EXCEPT 
                           ![i].msgs = Requesters[i].msgs \ {msg},
                           ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs>>
    
SendPostTasks(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \union
        {[type |-> "POST_TASKS", 
          pubkey |-> Requesters[i].pubkey, 
          tasks |-> Requesters[i].tasks]}]
    /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs>>
    
ReceivePostTasks(i) == 
    /\ Requesters[i].state = "RECV_POST_TASKS"
    /\ \E msg \in Requesters[i].msgs: msg.src = "TSSC"
    /\ \/ LET msg == CHOOSE m \in Requesters[i].msgs : m.src = "TSSC" IN 
          \/ /\ msg.type = "ACK"
             /\ Requesters' = [Requesters EXCEPT
                              ![i].tasks = {},
                              ![i].state = "SEND_QUERY_TASKS",
                              ![i].msgs = Requesters[i].msgs \ {msg}]
          \/ /\ msg.type = "INVALID"
             /\ Requesters' = [Requesters EXCEPT
                              ![i].state = "TERMINATED",
                              ![i].msgs = Requesters[i].msgs \ {msg}] 
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs>>
    
SendQueryTasks(i) == 
    /\ Requesters[i].state = "SEND_QUERY_TASKS"
    /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \union
        {[type |-> "QUERY_TASKS", 
          pubkey |-> Requesters[i].pubkey, 
          owner |-> Requesters[i].pubkey]}]
    /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs>>
    
GetFirstTask(msg) ==
    CHOOSE t \in msg.tasks : \A y \in msg.tasks : 
    t.taskId # y.taskId => t.taskId < y.taskId  
    
ReceiveQueryTasks_Success(i, msg) == 
    IF Cardinality(msg.tasks) = 0 
    THEN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                          ![i].tasks = msg.tasks,
                                          ![i].state = "TERMINATED"]
    ELSE LET firstTask == GetFirstTask(msg)
         IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                             ![i].tasks = msg.tasks \ {firstTask},
                                             ![i].unconfirmedWorkers = firstTask.participants, 
                                             ![i].confirmedWorkers = {},
                                             ![i].currentTask = firstTask,
                                             ![i].state = "SEND_KEY"]
    
ReceiveQueryTasks(i) == 
    /\ Requesters[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Requesters[i].msgs: msg.src = "TSSC"
    /\ \/ LET msg == CHOOSE m \in Requesters[i].msgs : m.src = "TSSC" IN
          \/ /\ msg.type = "TASKS"
             /\ ReceiveQueryTasks_Success(i, msg)
          \/ /\ msg.type = "INVALID"
             /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                 ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs>>

SendKey(i) ==
    /\ Requesters[i].state = "SEND_KEY"
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ LET nextWorkerPubkey == CHOOSE r \in Requesters[i].unconfirmedWorkers : TRUE IN 
        /\ LET wid == CHOOSE w \in 1..NumWorkers : Workers[w].pubkey = nextWorkerPubkey IN 
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union 
                                                        {[type |-> "SEND_KEY",
                                                         pubkey |-> Requesters[i].pubkey, 
                                                         keyshare |-> "PlaceholderKeyshare"]}]
            /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_KEY"]
    /\ UNCHANGED <<TSSC, TSCs, USSC, USCs>>

ReceiveKey(i) == 
    /\ Requesters[i].state = "RECV_KEY"
    /\ Cardinality(Requesters[i].unconfirmedWorkers) > 0
    /\ \E msg \in Requesters[i].msgs : /\ msg.type = "ACK" 
                                       /\ msg.pubkey \in Requesters[i].unconfirmedWorkers
    /\ LET msg == CHOOSE m \in Requesters[i].msgs : /\ m.type = "ACK" 
                                                    /\ m.pubkey \in Requesters[i].unconfirmedWorkers IN 
        /\ LET worker == CHOOSE w \in Requesters[i].unconfirmedWorkers : w = msg.pubkey IN 
            /\ Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg},
                                                ![i].unconfirmedWorkers = Requesters[i].unconfirmedWorkers \ {worker},
                                                ![i].confirmedWorkers = Requesters[i].confirmedWorkers \union {worker},
                                                ![i].state = IF Cardinality(Requesters[i].confirmedWorkers) + 1 = Cardinality(Requesters[i].currentTask.participants)
                                                             THEN "SEND_QUERY_HASHES"
                                                             ELSE "SEND_KEY"]
    /\ UNCHANGED <<Workers, TSSC, TSCs, USSC, USCs>>

SendQueryHashes(i) == 
    /\ Requesters[i].state = "SEND_QUERY_HASHES"
    /\ Requesters[i].currentTask.participants = Requesters[i].confirmedWorkers
    /\ LET tsc == CHOOSE t \in TSCs : t.pubkey = Requesters[i].currentTask.pubkey IN 
        /\ TSCs' = {IF t.taskId = Requesters[i].currentTask.taskId 
                    THEN [t EXCEPT !.msgs = t.msgs \union {[type |-> "QUERY_HASHES", pubkey |-> Requesters[i].pubkey]}]
                    ELSE t : t \in TSCs} 
        /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_QUERY_HASHES"]
    /\ UNCHANGED <<Workers, TSSC, USSC, USCs>>
    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> 

Terminated == 
    <>(\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")
            
Next == 
    \/ \E requester \in 1..NumRequesters : 
        \/ SendRegister(requester)
        \/ SendPostTasks(requester)
        \/ SendQueryTasks(requester)
        \/ SendKey(requester)
        \/ SendQueryHashes(requester)
        \/ ReceiveRegister(requester)        
        \/ ReceivePostTasks(requester)
        \/ ReceiveQueryTasks(requester)
        \/ ReceiveKey(requester)
    \/ Terminating
    


=============================================================================
\* Modification History
\* Last modified Sun Feb 25 10:10:05 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
