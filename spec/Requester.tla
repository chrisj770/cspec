----------------------------- MODULE Requester -----------------------------
EXTENDS Sequences, Common
        
RequesterTypeOK == 
    /\ \A requester \in Requesters : [requester.state ->
        {"INIT",            \* Initialize local variables
         "REGISTER",        \* Attempt to register as a REQUESTER via USSC
         "POST_TASKS",      \* Attempt to post a list of tasks via TSSC
         "QUERY_TASKS",     \* Request list of active tasks via TSSC
         "SEND_KEY",        \* Attempt to send key-share to WORKER for single task
         "QUERY_HASHES",    \* Request list of all hashes from TSC
         "QUERY_DATA",      \* Request all relevant sensory data from STORAGE
         "EVALUATE",        \* Run evaluation process
         "SUBMIT_EVAL",     \* Attempt to submit results of evaluation via TSC
         "SEND_WEIGHTS"}]   \* Attempt to broadcast weights received from evaluation
         
RequesterInit == 
    Requesters = [r \in 1..NumRequesters |-> [
                    msgs |-> <<>>, 
                    state |-> "INIT",
                    pubkey |-> ""]]
                    
RequesterSendRegister(i) == 
    /\ Requesters[i].state = "INIT"
    /\ Requesters' = [Requesters EXCEPT ![i].state = "REGISTER"]
    /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \o 
        <<[type |-> "REGISTER", userType |-> "REQUESTER", src |-> i]>>]
    /\ UNCHANGED <<Workers, USCs, TSSC, TSCs>>
    
RequesterReceiveRegister(i) == 
    /\ Requesters[i].state = "REGISTER"
    /\ Len(Requesters[i].msgs) > 0
    /\ LET msg == Head(Requesters[i].msgs) IN 
        /\ msg.src = "USSC"
        /\ msg.type = "REGISTERED"
        /\ Requesters' = [Requesters EXCEPT 
            ![i].pubkey = msg.pubkey, 
            ![i].msgs = Tail(Requesters[i].msgs),
            ![i].state = "POST_TASKS"]
    /\ UNCHANGED <<Workers, USSC, USCs, TSSC, TSCs>>
            
RequesterNext == 
    \E requester \in 1..NumRequesters : 
        \/ RequesterSendRegister(requester)
        \/ RequesterReceiveRegister(requester)

=============================================================================
\* Modification History
\* Last modified Thu Feb 22 16:12:28 CET 2024 by jungc
\* Created Thu Feb 22 09:05:46 CET 2024 by jungc
