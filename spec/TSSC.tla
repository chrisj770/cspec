-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, USSC, Common

CONSTANT TaskPostDeadline
ASSUME TaskPostDeadline >= RegistrationDeadline

TSSCTypeOK == 
    TSSC.state \in {"POST_TASKS", 
                    "WORKING"}

TSSCInit == 
    TSSC = [msgs |-> <<>>, 
           state |-> "POST_TASKS"]        
                    
TSSCSendResponse(pubkey, message) == 
    \/ /\ USSCCheckUser(pubkey, "REQUESTER")
       /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = pubkey IN
            /\ Len(Requesters[rid].msgs) = 0
            /\ Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \o message]
       /\ UNCHANGED <<Workers>>
    \/ /\ USSCCheckUser(pubkey, "WORKER")
       /\ LET wid == CHOOSE key \in DOMAIN Workers : Workers[key].pubkey = pubkey IN
            /\ Len(Workers[wid].msgs) = 0
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \o message]
       /\ UNCHANGED <<Requesters>>
        
TSSCReceivePostTasks == 
    /\ Len(TSSC.msgs) > 0
    /\ LET msg == Head(TSSC.msgs) IN
        /\ msg.type = "POST_TASKS"
        /\ \/ /\ Time < TaskPostDeadline 
              /\ Len(msg.tasks) > 0
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs)]
              /\ TSCPostTasks(msg.tasks, msg.pubkey)
              /\ TSSCSendResponse(msg.pubkey, <<[type |-> "ACK", src |-> "TSSC"]>>)                                  
           \/ /\ Time >= TaskPostDeadline
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs), !.state = "WORKING"]
              /\ TSSCSendResponse(msg.pubkey, <<[type |-> "INVALID", src |-> "TSSC"]>>)
              /\ UNCHANGED <<TSCs, NextPubkey>>
    /\ UNCHANGED <<USSC, USCs>>
    
TSSCReceiveQueryTasks == 
    /\ Len(TSSC.msgs) > 0
    /\ LET msg == Head(TSSC.msgs) IN 
        /\ msg.type = "QUERY_TASKS"
        /\ \/ /\ Time < TaskPostDeadline 
              /\ TSSCSendResponse(msg.pubkey, <<[type |-> "INVALID", src |-> "TSSC"]>>)
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs)] 
           \/ /\ Time >= TaskPostDeadline
              /\ \/ /\ msg.owner = NULL
                    /\ TSSCSendResponse(msg.pubkey, <<[type |-> "TASKS",  src |-> "TSSC", tasks |-> TSCs]>>)
                 \/ /\ msg.owner # NULL
                    /\ LET matchingTSCs == TSCs IN
                       TSSCSendResponse(msg.pubkey, <<[type |-> "TASKS",  src |-> "TSSC", tasks |-> matchingTSCs]>>)
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs), !.state = "WORKING"]
    /\ UNCHANGED <<TSCs, USSC, USCs>>
    
TSSCNext == 
    \/ TSSCReceivePostTasks
    \/ /\ TSSCReceiveQueryTasks
       /\ UNCHANGED <<NextPubkey>>

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:46:10 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
