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
    
QueryTasks_Requester(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ USSCCheckUser(msg.pubkey, "REQUESTER")
    /\ msg.owner # NULL
    /\ \A t \in TSCs : t.owner = msg.owner => t.state = "Unavailable"
    
QueryTasks_Worker(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ USSCCheckUser(msg.pubkey, "WORKER")
    /\ msg.owner = NULL
    
TSSCReceiveQueryTasks_Requester == 
    /\ \E msg \in TSSC.msgs : QueryTasks_Requester(msg)
    /\ LET msg == CHOOSE m \in TSSC.msgs : QueryTasks_Requester(m) IN 
        /\ LET matchingTSCs == TSCs IN 
           TSSCSendResponse(msg.pubkey, [type |-> "TASKS",  src |-> "TSSC", tasks |-> matchingTSCs])
        /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}] 
    /\ UNCHANGED <<TSCs, USSC, USCs>> 

TSSCReceiveQueryTasks_Worker == 
    /\ \E msg \in TSSC.msgs : QueryTasks_Worker(msg)
    /\ LET msg == CHOOSE m \in TSSC.msgs : QueryTasks_Worker(m) IN
        /\ TSSCSendResponse(msg.pubkey, [type |-> "TASKS",  src |-> "TSSC", tasks |-> TSCs])
        /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}]  
    /\ UNCHANGED <<TSCs, USSC, USCs>>            

(*
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
*) 
 
TSSCNext == 
    \/ TSSCReceivePostTasks
    \/ /\ \/ TSSCReceiveQueryTasks_Requester
          \/ TSSCReceiveQueryTasks_Worker
       /\ UNCHANGED <<NextPubkey>>

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 08:42:28 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
