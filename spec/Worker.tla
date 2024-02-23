------------------------------- MODULE Worker -------------------------------
EXTENDS Sequences, Common, Integers
    
WorkerTypeOK == 
    /\ \A worker \in Workers : [Workers.state -> 
        {"INIT",          \* Initialize local variables
         "REGISTER",      \* Attempt to register as a WORKER via USSC
         "QUERY_TASKS",   \* Request list of active tasks via TSSC
         "CONFIRM_TASK",  \* Attempt to enlist as a confirmed WORKER for each selected TSC
         "GET_KEY",       \* Await key-share from REQUESTER for single task
         "COMPUTE",       \* Generate sensory data
         "SUBMIT_DATA",   \* Attempt to submit encrypted sensory data to STORAGE
         "SUBMIT_HASH",   \* Attempt to submit hash of sensory data to TSC
         "GET_WEIGHTS",   \* Await weight broadcast from REQUESTER
         "QUERY_HASHES",  \* Request list of all hashes from TSC
         "QUERY_DATA",    \* Request all relevant sensory data from STORAGE
         "VERIFY",        \* Run verification process
         "SUBMIT_EVAL"}]  \* Attmept to submit evaluation results to TSC    
         
WorkerStateConsistency == TRUE
         
WorkerInit ==
    Workers = [w \in 1..NumWorkers |-> [
                msgs |-> <<>>, 
                state |-> "INIT",
                pubkey |-> ""]]
    
WorkerSendRegister(i) == 
    /\ Workers[i].state = "INIT"
    /\ Workers' = [Workers EXCEPT ![i].state = "REGISTER"]
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \o 
        <<[type |-> "REGISTER", userType |-> "WORKER", src |-> i]>>]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USCs>>
    
WorkerReceiveRegister(i) == 
    /\ Workers[i].state = "REGISTER"
    /\ Len(Workers[i].msgs) > 0
    /\ LET msg == Head(Workers[i].msgs) IN 
        /\ msg.src = "USSC"
        /\ msg.type = "REGISTERED"
        /\ Workers' = [Workers EXCEPT 
            ![i].pubkey = msg.pubkey, 
            ![i].msgs = Tail(Workers[i].msgs), 
            ![i].state = "QUERY_TASKS"]
    /\ UNCHANGED <<Requesters, TSSC, TSCs, USSC, USCs>>
    
WorkerTerminating == /\ \A w \in 1..NumWorkers: Workers[w].state = "QUERY_TASKS"
                     /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> 

WorkerTermination == <>(\A w \in 1..NumWorkers: Workers[w].state = "QUERY_TASKS")
        
WorkerNext == 
    \/ \E worker \in 1..NumWorkers : 
        \/ WorkerSendRegister(worker)
        \/ WorkerReceiveRegister(worker)
    \/ WorkerTerminating
        
=============================================================================
\* Modification History
\* Last modified Fri Feb 23 08:54:27 CET 2024 by jungc
\* Created Thu Feb 22 08:43:47 CET 2024 by jungc
