-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, USSC, TLC, Common 

TSCTypeOK == TRUE

TSCInit == TSCs = {}

GetIndex(task, allTasks) == 
    CHOOSE i \in DOMAIN allTasks : allTasks[i] = task
    
AddFields(struct, id, owner) == 
    struct @@ [taskId |-> id,
               pubkey |-> ToString(NextPubkey + id),
               category |-> "Placeholder",
               state |-> "Available",
               owner |-> owner,
               participants |-> <<>>,
               numParticipants |-> 1,
               globalReputationThreshold |-> 0,
               expertiseReputationThreshold |-> 0,
               checkQ |-> [j \in 0..1 |-> TRUE],
               QEvaluate |-> [j \in 0..1 |-> TRUE],
               msgs |-> {}]

TSCPostTasks(tasks, owner) == 
    LET addTSCs == {AddFields(s, i, owner) : 
                    s \in tasks, 
                    i \in Cardinality(TSCs)..(Cardinality(TSCs)+Cardinality(tasks)-1)}    
    IN /\ TSCs' = TSCs \union addTSCs
       /\ NextPubkey' = NextPubkey + Cardinality(tasks) 
    
TSCSendResponse(pubkey, message) == 
    \/ /\ USSCCheckUser(pubkey, "REQUESTER")
       /\ LET rid == CHOOSE key \in DOMAIN Requesters : Requesters[key].pubkey = pubkey IN
            /\ Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
       /\ UNCHANGED <<Workers>>
    \/ /\ USSCCheckUser(pubkey, "WORKER")
       /\ LET wid == CHOOSE key \in DOMAIN Workers : Workers[key].pubkey = pubkey IN
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
       /\ UNCHANGED <<Requesters>>

TSCConfirmTask_CanParticipate(msg, tsc) == 
    /\ Len(tsc.participants) < tsc.numParticipants
    /\ tsc.checkQ[USSCGetUser(msg.pubkey, "WORKER").info.reputation]
    
TSCConfirmTask_AddParticipant(msg, tsc) == 
    /\ TSCs' = {IF t.taskId = tsc.taskId
                THEN [t EXCEPT !.msgs = t.msgs \ {msg}, 
                               !.participants = tsc.participants \o <<USSCGetUser(msg.pubkey, "WORKER").info.pubkey>>,
                               !.state = IF Len(tsc.participants) + 1 = tsc.numParticipants
                                         THEN "Unavailable" ELSE "Available"]
                ELSE t : t \in TSCs}
              
TSCConfirmTask == 
    /\ \E t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK"
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK" IN 
        /\ LET msg == CHOOSE m \in tsc.msgs : m.type = "CONFIRM_TASK" IN 
            /\ USSCCheckUser(msg.pubkey, "WORKER")
            /\ \/ /\ \/ /\ tsc.state \in {"Pending", "Unavailable", "QEvaluating"}
                        /\ TSCSendResponse(msg.pubkey, [type |-> "INVALID", pubkey |-> tsc.pubkey])
                     \/ /\ tsc.state = "Canceled"
                        /\ TSCSendResponse(msg.pubkey, [type |-> "CANCELED", pubkey |-> tsc.pubkey])
                     \/ /\ tsc.state = "Completed"
                        /\ TSCSendResponse(msg.pubkey, [type |-> "COMPLETED", pubkey |-> tsc.pubkey])
                  /\ TSCs' = {IF t.taskId = tsc.taskId
                              THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
                              ELSE t : t \in TSCs}
               \/ /\ tsc.state = "Available"
                  /\ IF TSCConfirmTask_CanParticipate(msg, tsc) 
                     THEN /\ TSCConfirmTask_AddParticipant(msg, tsc)
                          /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_SUCCESS", pubkey |-> tsc.pubkey])                    
                     ELSE /\ TSCs' = {IF t.taskId = tsc.taskId
                                      THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
                                      ELSE t : t \in TSCs} 
                          /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_FAIL", pubkey |-> tsc.pubkey])
    /\ UNCHANGED <<TSSC, USSC, USCs>>


TSCNext == \/ /\ Cardinality(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ TSCConfirmTask
            \* \/ TSCUnavailable(tsc)
            \* \/ TSCQEvaluating(tsc)

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 17:02:50 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
