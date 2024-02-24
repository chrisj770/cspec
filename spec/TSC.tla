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
                    i \in Cardinality(TSCs)..Cardinality(TSCs)+Cardinality(tasks)}    
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

TSCConfirmTask_Success(msg, tsc) == 
    /\ Len(tsc.participants) < tsc.numParticipants
    /\ LET user == USSCGetUser(msg.pubkey, "WORKER") IN
        /\ tsc.checkQ[user.info.reputation]
        /\ TSCs' = {IF t.taskId = tsc.taskId
                    THEN [t EXCEPT !.msgs = t.msgs \ {msg}, 
                                   !.participants = tsc.participants \o <<user.info.pubkey>>,
                                   !.state = IF Len(tsc.participants) + 1 = tsc.numParticipants
                                             THEN "Unavailable" ELSE "Available"]
                    ELSE t : t \in TSCs}
    /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_SUCCESS", src |-> tsc.pubkey])
              
TSCConfirmTask == 
    /\ \E t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK"
    /\ LET tsc == CHOOSE t \in TSCs : \E msg \in t.msgs : msg.type = "CONFIRM_TASK" IN 
        /\ LET msg == CHOOSE m \in tsc.msgs : m.type = "CONFIRM_TASK" IN 
            /\ USSCCheckUser(msg.pubkey, "WORKER")
            /\ \/ /\ \/ /\ tsc.state \in {"Pending", "Unavailable", "QEvaluating"}
                        /\ TSCSendResponse(msg.pubkey, [type |-> "INVALID", src |-> tsc.pubkey])
                     \/ /\ tsc.state = "Canceled"
                        /\ TSCSendResponse(msg.pubkey, [type |-> "CANCELED", src |-> tsc.pubkey])
                     \/ /\ tsc.state = "Completed"
                        /\ TSCSendResponse(msg.pubkey, [type |-> "COMPLETED", src |-> tsc.pubkey])
                  /\ TSCs' = {IF t.taskId = tsc.taskId
                              THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
                              ELSE t : t \in TSCs}
               \/ /\ tsc.state = "Available"
                  /\ \/ TSCConfirmTask_Success(msg, tsc)
                     \/ /\ TSCSendResponse(msg.pubkey, [type |-> "CONFIRM_FAIL", src |-> tsc.pubkey])
                        /\ TSCs' = {IF t.taskId = tsc.taskId
                                    THEN [t EXCEPT !.msgs = t.msgs \ {msg}]
                                    ELSE t : t \in TSCs}
    /\ UNCHANGED <<TSSC, USSC, USCs>>


TSCNext == \/ /\ Cardinality(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ TSCConfirmTask
            \* \/ TSCUnavailable(tsc)
            \* \/ TSCQEvaluating(tsc)

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 15:22:40 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
