-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, Common

CONSTANT TaskPostDeadline
ASSUME TaskPostDeadline >= RegistrationDeadline

TSSCTypeOK == 
    TSSC.state \in {"POST_TASKS", 
                    "WORKING"}

TSSCInit == 
    TSSC = [msgs |-> {}]    
                   
TSSCReceivePostTasks_MessageFormat(msg) == 
    /\ msg.type = "POST_TASKS"
    /\ IsRequester(msg.pubkey)

TSSCReceivePostTasks_IsEnabled == 
    /\ \E msg \in TSSC.msgs :TSSCReceivePostTasks_MessageFormat(msg)

TSSCReceivePostTasks == 
    /\ TSSCReceivePostTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSSC.msgs : TSSCReceivePostTasks_MessageFormat(m) 
       IN IF Time < TaskPostDeadline 
          THEN /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}]
               /\ TSCPostTasks(msg.tasks, msg.pubkey)
               /\ SendMessage(msg.pubkey, [type |-> "ACK", src |-> "TSSC"])                                  
          ELSE /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}]
               /\ SendMessage(msg.pubkey, [type |-> "INVALID", src |-> "TSSC"])
               /\ UNCHANGED <<TSCs, NextPubkey>>
    /\ UNCHANGED <<Workers, USSC, USCs>>

TSSCQueryTasks_MessageFormat(msg) == 
    /\ msg.type = "QUERY_TASKS" 
    /\ \/ /\ IsRequester(msg.pubkey)
          /\ msg.owner # NULL
          /\ \A t \in TSCs : t.owner = msg.owner => t.state = "Unavailable"
       \/ /\ IsWorker(msg.pubkey)
          /\ msg.owner = NULL

TSSCQueryTasks_IsEnabled == 
    /\ \E msg \in TSSC.msgs : TSSCQueryTasks_MessageFormat(msg)

TSSCReceiveQueryTasks == 
    /\ TSSCQueryTasks_IsEnabled
    /\ LET msg == CHOOSE m \in TSSC.msgs : TSSCQueryTasks_MessageFormat(m)
           matchingTSCs == IF IsWorker(msg.pubkey) THEN TSCs
                           ELSE {t \in TSCs : t.owner = msg.owner} 
       IN /\ SendMessage(msg.pubkey, [type |-> "TASKS",  src |-> "TSSC", tasks |-> matchingTSCs])
          /\ TSSC' = [TSSC EXCEPT !.msgs = TSSC.msgs \ {msg}]
          /\ IF IsRequester(msg.pubkey) 
             THEN UNCHANGED <<Workers>>
             ELSE UNCHANGED <<Requesters>> 
    /\ UNCHANGED <<TSCs, USSC, USCs>>           

TSSCNext == 
    \/ TSSCReceivePostTasks
    \/ /\ TSSCReceiveQueryTasks
       /\ UNCHANGED <<NextPubkey>>

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 15:10:15 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
