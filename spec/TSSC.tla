-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, USSC, Common

TSSCTypeOK == TSSC.state \in {"INIT", "POST_TASKS", "WORKING"}

TSSCInit == TSSC = [msgs |-> <<>>, 
                    state |-> "INIT"]
        
TSSCReceivePost(msg) == 
    /\ \/ TSSC.state = "INIT"
       \/ TSSC.state = "POST_TASKS"
    /\ USSCGetUser(msg.pubkey, "REQUESTER")
    /\ TSCs' = TSCs \o msg.tasks
    /\ TSSC' = [TSSC EXCEPT !.state = "POST_TASKS", !.msgs = Tail(TSSC.msgs)]
    /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = msg.pubkey IN
           Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \o 
                         <<[type |-> "ACK", src |-> "TSSC"]>>]
    /\ UNCHANGED <<Workers, USSC, USCs>>
   
TSSCReceiveQuery(msg) == TRUE
TSSCReceiveInvalid(msg) == TRUE
    
TSSCReceive == 
    /\ Len(TSSC.msgs) > 0
    /\ LET message == Head(TSSC.msgs) IN
        IF message.type = "POST_TASKS" THEN TSSCReceivePost(message)
        ELSE IF message.type = "QUERY_TASKS" THEN TSSCReceiveQuery(message)
        ELSE TSSCReceiveInvalid(message)
    
TSSCNext == 
    \/ TSSCReceive

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 09:54:04 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
