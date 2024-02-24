------------------------------- MODULE Worker -------------------------------
EXTENDS FiniteSets, Sequences, Common, Integers
    
TypeOK == 
    /\ \A worker \in Workers : [Workers.state -> 
        {"INIT",                \* Initialize local variables
         "SEND_REGISTER",       \* Attempt to register as a WORKER via USSC
         "RECV_REGISTER",       \* Receive acknowledgement and public/private key from USSC 
         "SEND_QUERY_TASKS",    \* Request list of active tasks via TSSC
         "RECV_QUERY_TASKS",    \* Receive list of active tasks from TSSC, or INVALID
         "SEND_CONFIRM_TASK",   \* Attempt to enlist as a confirmed WORKER for each selected TSC
         "GET_KEY",             \* Await key-share from REQUESTER for single task
         "COMPUTE",             \* Generate sensory data
         "SUBMIT_DATA",         \* Attempt to submit encrypted sensory data to STORAGE
         "SUBMIT_HASH",         \* Attempt to submit hash of sensory data to TSC
         "GET_WEIGHTS",         \* Await weight broadcast from REQUESTER
         "QUERY_HASHES",        \* Request list of all hashes from TSC
         "QUERY_DATA",          \* Request all relevant sensory data from STORAGE
         "VERIFY",              \* Run verification process
         "SUBMIT_EVAL",         \* Attempt to submit evaluation results to TSC  
         "TERMINATED"}]         \*
         
StateConsistency == TRUE
         
Init ==
    Workers = [w \in 1..NumWorkers |-> [
                msgs |-> {}, 
                state |-> "SEND_REGISTER",
                pubkey |-> "",
                unconfirmedTasks |-> {}, 
                confirmedTasks |-> {}]]
    
SendRegister(i) == 
    /\ Workers[i].state = "SEND_REGISTER"
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \union 
        {[type |-> "REGISTER", 
          userType |-> "WORKER", 
          src |-> i]}]
    /\ Workers' = [Workers EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USCs>>
    
ReceiveRegister(i) == 
    /\ Workers[i].state = "RECV_REGISTER"
    /\ \E msg \in Workers[i].msgs : msg.src = "USSC"
    /\ LET msg == CHOOSE m \in Workers[i].msgs : m.src = "USSC" IN
        \/ /\ msg.type = "REGISTERED"
           /\ Workers' = [Workers EXCEPT 
                         ![i].pubkey = msg.pubkey, 
                         ![i].msgs = Workers[i].msgs \ {msg}, 
                         ![i].state = "SEND_QUERY_TASKS"]
        \/ /\ msg.type = "NOT_REGISTERED"
           /\ Workers' = [Workers EXCEPT
                         ![i].msgs = Workers[i].msgs \ {msg}, 
                         ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
SendQueryTasks(i) == 
    /\ Workers[i].state = "SEND_QUERY_TASKS"
    /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \union
                {[type |-> "QUERY_TASKS", 
                   pubkey |-> Workers[i].pubkey,
                   owner |-> NULL]}]
    /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSCs, USSC, USCs>>
    
ReceiveQueryTasks_Success(i, msg) == 
    Workers' = [Workers EXCEPT 
                ![i].msgs = Workers[i].msgs \ {msg},
                ![i].unconfirmedTasks = msg.tasks,
                ![i].state = IF Cardinality(msg.tasks) > 0
                             THEN "SEND_CONFIRM_TASK"
                             ELSE "TERMINATED"]
    
ReceiveQueryTasks(i) == 
    /\ Workers[i].state = "RECV_QUERY_TASKS"
    /\ \E msg \in Workers[i].msgs : msg.src = "TSSC"
    /\ LET msg == CHOOSE m \in Workers[i].msgs : m.src = "TSSC" IN
        \/ /\ msg.type = "TASKS"
           /\ ReceiveQueryTasks_Success(i, msg)
        \/ /\ msg.type = "INVALID"
           /\ Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg},
                                         ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
SendConfirmTask(i) == 
    /\ Workers[i].state = "SEND_CONFIRM_TASK" 
    /\ LET currTask == CHOOSE tsc \in Workers[i].unconfirmedTasks :
                       \A other \in Workers[i].unconfirmedTasks: 
                       tsc # other => tsc.taskId < other.taskId IN 
        /\ TSCs' = {IF t.taskId = currTask.taskId 
                    THEN [t EXCEPT !.msgs = t.msgs \union {[type |-> "CONFIRM_TASK", pubkey |-> Workers[i].pubkey]}]
                    ELSE t : t \in TSCs}
    /\ Workers' = [Workers EXCEPT ![i].state = "RECV_CONFIRM_TASK"]
    /\ UNCHANGED <<Requesters, TSSC, USSC, USCs>>
    
ReceiveConfirmTask_Failed(i, msg, task) == 
    Workers' = [Workers EXCEPT 
                ![i].msgs = Workers[i].msgs \ {msg},
                ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId},
                ![i].state = IF Cardinality(Workers[i].unconfirmedTasks) = 1
                             THEN IF Cardinality(Workers[i].confirmedTasks) > 0
                                  THEN "GET_KEY"
                                  ELSE "SEND_QUERY_TASK"
                             ELSE "SEND_CONFIRM_TASK"]

ReceiveConfirmTask_Success(i, msg, task) ==   
    Workers' = [Workers EXCEPT 
                ![i].msgs = Workers[i].msgs \ {msg},
                ![i].unconfirmedTasks = {t \in Workers[i].unconfirmedTasks : t.taskId # task.taskId}, 
                ![i].confirmedTasks = Workers[i].confirmedTasks \union {task},
                ![i].state = IF Cardinality(Workers[i].unconfirmedTasks) = 1
                             THEN "GET_KEY"
                             ELSE "SEND_CONFIRM_TASK"]

ReceiveConfirmTask(i) == 
    /\ Workers[i].state = "RECV_CONFIRM_TASK"
    /\ \E msg \in Workers[i].msgs : msg.src \in {t.pubkey : t \in Workers[i].unconfirmedTasks}
    /\ LET msg == CHOOSE m \in Workers[i].msgs : m.src \in {t.pubkey : t \in Workers[i].unconfirmedTasks}
           task == CHOOSE t \in Workers[i].unconfirmedTasks : t.pubkey = msg.src IN 
        \/ /\ msg.type \in {"INVALID", "CONFIRM_FAIL", "CANCELED", "COMPLETED"}
           /\ ReceiveConfirmTask_Failed(i, msg, task)
        \/ /\ msg.type = "CONFIRM_SUCCESS" 
           /\ ReceiveConfirmTask_Success(i, msg, task)
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
    
Terminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> 

Terminated == <>(\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")
        
Next == 
    \/ \E worker \in 1..NumWorkers : 
        \/ SendRegister(worker)
        \/ SendQueryTasks(worker)
        \/ SendConfirmTask(worker)        
        \/ ReceiveRegister(worker)
        \/ ReceiveQueryTasks(worker)
        \/ ReceiveConfirmTask(worker)
    \/ Terminating
        
=============================================================================
\* Modification History
\* Last modified Sat Feb 24 15:25:12 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
