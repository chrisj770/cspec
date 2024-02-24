-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, USSC, TLC, Common 

TSCTypeOK == TRUE

TSCInit == TSCs = <<>>

GetIndex(task, allTasks) == 
    CHOOSE i \in DOMAIN allTasks : allTasks[i] = task

TSCPostTasks(tasks, owner) == 
    LET nTasks == [i \in 1..Len(tasks) |-> tasks[i] @@ [ 
                    taskId |-> GetIndex(tasks[i], tasks) + Len(TSCs),
                    pubkey |-> ToString(NextPubkey + GetIndex(tasks[i], tasks)-1),
                    category |-> "Placeholder",
                    state |-> "Available",
                    owner |-> owner,
                    participants |-> <<>>,
                    numParticipants |-> 1,
                    globalReputationThreshold |-> 0,
                    expertiseReputationThreshold |-> 0,
                    checkQ |-> [j \in 0..1 |-> TRUE],
                    QEvaluate |-> [j \in 0..1 |-> TRUE],
                    msgs |-> <<>>]]
    IN /\ TSCs' = TSCs \o nTasks
       /\ NextPubkey' = NextPubkey + Len(tasks)
    
TSCSendResponse(pubkey, message) == 
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

TSCConfirmTask_Success(i, msg, tsc) == 
   /\ Len(tsc.participants) < tsc.numParticipants
   /\ LET user == USSCGetUser(msg.pubkey, "WORKER") IN
        /\ tsc.checkQ[user.info.reputation]
        /\ TSCs' = [TSCs EXCEPT ![i].msgs = Tail(tsc.msgs),
                                ![i].participants = tsc.participants \o <<user.info.pubkey>>,
                                ![i].state = IF Len(tsc.participants) + 1 = tsc.numParticipants
                                             THEN "Unavailable" ELSE "Available"]
   /\ TSCSendResponse(msg.pubkey, <<[type |-> "CONFIRM_SUCCESS", src |-> tsc.pubkey]>>)
              
TSCConfirmTask(i) == 
    /\ LET tsc == TSCs[i] IN
        /\ Len(tsc.msgs) > 0
        /\ USSCCheckUser(Head(tsc.msgs).pubkey, "WORKER")
        /\ LET msg == Head(tsc.msgs) IN 
            \/ /\ \/ /\ tsc.state \in {"Pending", "Unavailable", "QEvaluating"}
                     /\ TSCSendResponse(msg.pubkey, <<[type |-> "INVALID", src |-> tsc.pubkey]>>)
                  \/ /\ tsc.state = "Canceled"
                     /\ TSCSendResponse(msg.pubkey, <<[type |-> "CANCELED", src |-> tsc.pubkey]>>)
                  \/ /\ tsc.state = "Completed"
                     /\ TSCSendResponse(msg.pubkey, <<[type |-> "COMPLETED", src |-> tsc.pubkey]>>)
               /\ TSCs' = [TSCs EXCEPT ![i].msgs = Tail(tsc.msgs)]
            \/ /\ tsc.state = "Available"
               /\ \/ TSCConfirmTask_Success(i, msg, tsc)
                  \/ /\ TSCSendResponse(msg.pubkey, <<[type |-> "CONFIRM_FAIL", src |-> tsc.pubkey]>>)
                     /\ TSCs' = [TSCs EXCEPT ![i].msgs = Tail(tsc.msgs)]
    /\ UNCHANGED <<TSSC, USSC, USCs>>


TSCNext == \/ /\ Len(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ \E tsc \in 1..Len(TSCs) : 
               \/ TSCConfirmTask(tsc)
            \* \/ TSCUnavailable(tsc)
            \* \/ TSCQEvaluating(tsc)

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:55:29 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
