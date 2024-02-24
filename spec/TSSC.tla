-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, USSC, Common

CONSTANT TaskPostDeadline
ASSUME TaskPostDeadline >= RegistrationDeadline

TSSCTypeOK == 
    TSSC.state \in {"POST_TASKS", 
                    "WORKING"}

TSSCInit == 
    TSSC = [msgs |-> {}, 
           state |-> "POST_TASKS"]        
                    
TSSCSendResponse(pubkey, message) == 
    \/ /\ USSCCheckUser(pubkey, "REQUESTER")
       /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = pubkey IN
            /\ Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
       /\ UNCHANGED <<Workers>>
    \/ /\ USSCCheckUser(pubkey, "WORKER")
       /\ LET wid == CHOOSE key \in DOMAIN Workers : Workers[key].pubkey = pubkey IN
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
       /\ UNCHANGED <<Requesters>>
        
TSSCReceivePostTasks == 
    /\ \E msg \in TSSC.msgs : msg.type = "POST_TASKS"
    /\ LET msg == CHOOSE m \in TSSC.msgs : m.type = "POST_TASKS" IN
        \/ /\ Time < TaskPostDeadline 
           /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}]
           /\ TSCPostTasks(msg.tasks, msg.pubkey)
           /\ TSSCSendResponse(msg.pubkey, [type |-> "ACK", src |-> "TSSC"])                                  
        \/ /\ Time >= TaskPostDeadline
           /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}, !.state = "WORKING"]
           /\ TSSCSendResponse(msg.pubkey, [type |-> "INVALID", src |-> "TSSC"])
           /\ UNCHANGED <<TSCs, NextPubkey>>
    /\ UNCHANGED <<USSC, USCs>>
    
TSSCReceiveQueryTasks_Requester(msg) == 
    /\ msg.owner # NULL
    /\ \A i \in 1..Len(TSCs) : TSCs[i].pubkey = msg.owner => TSCs[i].state = "Unavailable"
    /\ LET matchingTSCs == TSCs IN 
       TSSCSendResponse(msg.pubkey, [type |-> "TASKS",  src |-> "TSSC", tasks |-> matchingTSCs]) 

TSSCReceiveQueryTasks_Worker(msg) == 
    /\ msg.owner = NULL 
    /\ TSSCSendResponse(msg.pubkey, [type |-> "TASKS",  src |-> "TSSC", tasks |-> TSCs])                  

TSSCReceiveQueryTasks == 
    /\ \E msg \in TSSC.msgs : msg.type = "QUERY_TASKS"
    /\ LET msg == CHOOSE m \in TSSC.msgs : m.type = "QUERY_TASKS" IN     
        \/ /\ Time < TaskPostDeadline 
           /\ TSSCSendResponse(msg.pubkey, [type |-> "INVALID", src |-> "TSSC"])
           /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}] 
        \/ /\ Time >= TaskPostDeadline
           /\ \/ /\ USSCCheckUser(msg.pubkey, "REQUESTER")
                 /\ TSSCReceiveQueryTasks_Requester(msg)
              \/ /\ USSCCheckUser(msg.pubkey, "WORKER")
                 /\ TSSCReceiveQueryTasks_Worker(msg)
           /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}, !.state = "WORKING"]
    /\ UNCHANGED <<TSCs, USSC, USCs>>
    
TSSCNext == 
    \/ TSSCReceivePostTasks
    \/ /\ TSSCReceiveQueryTasks
       /\ UNCHANGED <<NextPubkey>>

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 13:35:44 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
