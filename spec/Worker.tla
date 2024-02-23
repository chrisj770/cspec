------------------------------- MODULE Worker -------------------------------
EXTENDS Sequences, Common, Integers
    
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
                msgs |-> <<>>, 
                state |-> "SEND_REGISTER",
                pubkey |-> "",
                unconfirmedTasks |-> <<>>, 
                confirmedTasks |-> <<>>]]
    
SendRegister(i) == 
    /\ Workers[i].state = "SEND_REGISTER"
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \o 
        <<[type |-> "REGISTER", userType |-> "WORKER", src |-> i]>>]
    /\ Workers' = [Workers EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USCs>>
    
ReceiveRegister(i) == 
    /\ Workers[i].state = "RECV_REGISTER"
    /\ Len(Workers[i].msgs) > 0
    /\ LET msg == Head(Workers[i].msgs) IN 
        /\ msg.src = "USSC"
        /\ msg.type = "REGISTERED"
        /\ Workers' = [Workers EXCEPT 
            ![i].pubkey = msg.pubkey, 
            ![i].msgs = Tail(Workers[i].msgs), 
            ![i].state = "SEND_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
SendQueryTasks(i) == 
    /\ Workers[i].state = "SEND_QUERY_TASKS"
    /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \o
        <<[type |-> "QUERY_TASKS", 
          pubkey |-> Workers[i].pubkey]>>]
    /\ Workers' = [Workers EXCEPT ![i].state = "RECV_QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSCs, USSC, USCs>>
    
ReceiveQueryTasks(i) == 
    /\ Workers[i].state = "RECV_QUERY_TASKS"
    /\ Len(Workers[i].msgs) > 0
    /\ LET msg == Head(Workers[i].msgs) IN 
        /\ msg.src = "TSSC"
        /\ \/ /\ msg.type = "INVALID"
              /\ Workers' = [Workers EXCEPT ![i].msgs = Tail(Workers[i].msgs),
                                            ![i].state = "SEND_QUERY_TASKS"]
           \/ /\ msg.type = "TASKS"
              /\ \/ /\ Len(msg.tasks) > 0
                    /\ Workers' = [Workers EXCEPT ![i].msgs = Tail(Workers[i].msgs),
                                                  ![i].unconfirmedTasks = Workers[i].unconfirmedTasks \o msg.tasks,
                                                  ![i].state = "SEND_CONFIRM_TASK"]
                 \/ /\ Len(msg.tasks) = 0
                    /\ Workers' = [Workers EXCEPT ![i].msgs = Tail(Workers[i].msgs),
                                                  ![i].state = "TERMINATED"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
Terminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "TERMINATED"
               /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> 

Terminated == <>(\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")
        
Next == 
    \/ \E worker \in 1..NumWorkers : 
        \/ SendRegister(worker)
        \/ ReceiveRegister(worker)
        \/ SendQueryTasks(worker)
        \/ ReceiveQueryTasks(worker)
    \/ Terminating
        
=============================================================================
\* Modification History
\* Last modified Fri Feb 23 14:31:45 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
