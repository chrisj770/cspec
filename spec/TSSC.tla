-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, USSC, Common

CONSTANT TaskPostDeadline
ASSUME TaskPostDeadline >= RegistrationDeadline

TypeOK == 
    TSSC.state \in {"POST_TASKS", 
                    "WORKING"}

Init == 
    TSSC = [msgs |-> <<>>, 
           state |-> "POST_TASKS"]        
                    
SendResponse(pubkey, message) == 
    \/ /\ USSCGetUser(pubkey, "REQUESTER")
       /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = pubkey IN
              Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \o message]
       /\ UNCHANGED <<Workers>>
    \/ /\ USSCGetUser(pubkey, "WORKER")
       /\ LET wid == CHOOSE key \in DOMAIN Workers : Workers[key].pubkey = pubkey IN
              Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \o message]
       /\ UNCHANGED <<Requesters>>
        
ReceivePostTasks == 
    /\ \/ TSSC.state = "POST_TASKS"
       \/ TSSC.state = "WORKING"
    /\ Len(TSSC.msgs) > 0
    /\ LET msg == Head(TSSC.msgs) IN
        /\ msg.type = "POST_TASKS"
        /\ \/ /\ Time < TaskPostDeadline 
              /\ Len(msg.tasks) > 0
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs)]
              /\ TSCs' = TSCs \o msg.tasks
              /\ SendResponse(msg.pubkey, <<[type |-> "ACK", src |-> "TSSC"]>>)                                  
           \/ /\ Time >= TaskPostDeadline
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs), !.state = "WORKING"]
              /\ SendResponse(msg.pubkey, <<[type |-> "INVALID", src |-> "TSSC"]>>)
              /\ UNCHANGED <<TSCs>>
    /\ UNCHANGED <<USSC, USCs>>
    
ReceiveQueryTasks == 
    /\ \/ TSSC.state = "POST_TASKS"
       \/ TSSC.state = "WORKING"
    /\ Len(TSSC.msgs) > 0
    /\ LET msg == Head(TSSC.msgs) IN 
        /\ msg.type = "QUERY_TASKS"
        /\ \/ /\ Time < TaskPostDeadline 
              /\ SendResponse(msg.pubkey, <<[type |-> "INVALID", src |-> "TSSC"]>>)
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs)] 
           \/ /\ Time >= TaskPostDeadline
              /\ SendResponse(msg.pubkey, <<[type |-> "TASKS", src |-> "TSSC", tasks |-> TSCs]>>)
              /\ TSSC' = [TSSC EXCEPT !.msgs = Tail(TSSC.msgs), !.state = "WORKING"]
    /\ UNCHANGED <<TSCs, USSC, USCs>>
    
Next == 
    \/ ReceivePostTasks
    \/ ReceiveQueryTasks

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 15:32:11 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
