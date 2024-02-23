----------------------------- MODULE Requester -----------------------------
EXTENDS Sequences, Common

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
         "QUERY_HASHES",        \* Request list of all hashes from TSC
         "QUERY_DATA",          \* Request all relevant sensory data from STORAGE
         "EVALUATE",            \* Run evaluation process
         "SUBMIT_EVAL",         \* Attempt to submit results of evaluation via TSC
         "SEND_WEIGHTS",        \* Attempt to broadcast weights received from evaluation
         "TERMINATED"}]       
         
Init == 
    Requesters = [r \in 1..NumRequesters |-> [
                    msgs |-> <<>>, 
                    state |-> "SEND_REGISTER",
                    pubkey |-> "",
                    tasks |-> Tasks]]
                    
SendRegister(i) == 
    /\ Requesters[i].state = "SEND_REGISTER"
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \o 
        <<[type |-> "REGISTER", 
          userType |-> "REQUESTER", 
          src |-> i]>>]
    /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_REGISTER"]
    /\ UNCHANGED <<Workers, USCs, TSSC, TSCs>>
    
ReceiveRegister(i) == 
    /\ Requesters[i].state = "RECV_REGISTER"
    /\ Len(Requesters[i].msgs) > 0
    /\ LET msg == Head(Requesters[i].msgs) IN 
        /\ msg.src = "USSC"
        /\ msg.type = "REGISTERED"
        /\ Requesters' = [Requesters EXCEPT 
            ![i].pubkey = msg.pubkey, 
            ![i].msgs = Tail(Requesters[i].msgs),
            ![i].state = "SEND_POST_TASKS"]
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs>>
    
SendPostTasks(i) == 
    /\ Requesters[i].state = "SEND_POST_TASKS"
    /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \o
        <<[type |-> "POST_TASKS", 
          pubkey |-> Requesters[i].pubkey, 
          tasks |-> Requesters[i].tasks]>>]
    /\ Requesters' = [Requesters EXCEPT ![i].state = "RECV_POST_TASKS"]
    /\ UNCHANGED <<Workers, TSCs, USSC, USCs>>
    
ReceivePostTasks(i) == 
    /\ Requesters[i].state = "RECV_POST_TASKS"
    /\ Len(Requesters[i].msgs) > 0
    /\ LET msg == Head(Requesters[i].msgs) IN 
        /\ msg.src = "TSSC"
        /\ msg.type = "ACK"
        /\ Requesters' = [Requesters EXCEPT
            ![i].tasks = <<>>,
            ![i].state = "SEND_QUERY_TASKS",
            ![i].msgs = Tail(Requesters[i].msgs)]
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs>>
    
Terminating == 
    /\ \A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED"
    /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> 

Terminated == 
    <>(\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")
            
Next == 
    \/ \E requester \in 1..NumRequesters : 
        \/ SendRegister(requester)
        \/ SendPostTasks(requester)
        \/ ReceiveRegister(requester)        
        \/ ReceivePostTasks(requester)
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 14:31:16 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
