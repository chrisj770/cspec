----------------------- MODULE _Properties_Requester -----------------------
EXTENDS Requester, _Properties

(***************************************************************************)
(*                             STATE CONSISTENCY                           *)
(***************************************************************************)
AllowedStateTransitions == {
   [start |-> "INIT",               \* INIT: Initialize local variables
      end |-> {"SEND_REGISTER",     \* Transitions upon completing initialization
               "TERMINATED"}],      \* Transitions upon global timeout  
      
   [start |-> "SEND_REGISTER",      \* SEND_REGISTER: Attempt to register with USC
      end |-> {"RECV_REGISTER",     \* Transitions upon sending "REGISTER" message
               "TERMINATED"}],      \* Transitions upon global timeout 
      
   [start |-> "RECV_REGISTER",      \* RECV_REGISTER: Await registration information from USC
      end |-> {"SEND_POST_TASKS",   \* Transitions upon receiving "REGISTERED" with key-share info
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED", or global timeout
      
   [start |-> "SEND_POST_TASKS",    \* SEND_POST_TASKS: Send all pending tasks to TSC
      end |-> {"RECV_POST_TASKS",   \* Transitions upon sending "POST_TASKS" message
               "TERMINATED"}],      \* Transitions upon global timeout  
      
   [start |-> "RECV_POST_TASKS",    \* RECV_POST_TASKS: Await acknowledgement of "POST_TASKS" message from TSC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "ACK" from TSC
               "TERMINATED"}],      \* Transitions upon receiving "INVALID" (i.e. TaskPostDeadline has elapsed), or global timeout
      
   [start |-> "SEND_QUERY_TASKS",   \* SEND_QUERY_TASKS: Send message to query tasks via TSC
      end |-> {"RECV_QUERY_TASKS",  \* Transitions upon sending "QUERY_TASKS" message
               "TERMINATED"}],      \* Transitions upon global timeout 
      
   [start |-> "RECV_QUERY_TASKS",   \* RECV_QUERY_TASKS: Await updated task information from TSC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "INVALID" or a non-empty task list, w/o state="Unavailable"
               "SEND_KEY",          \* Transitions upon receiving "TASKS" with non-empty task list, all w/ state="Unavailable"
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED" or an empty task list, or global timeout
      
   [start |-> "SEND_KEY",           \* SEND_KEY: Split private key and send to next WORKER
      end |-> {"RECV_KEY",          \* Transitions upon sending "SEND_KEY" message with key-share
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "RECV_KEY",           \* RECV_KEY: Await acknowledgement of key-share from WORKER
      end |-> {"SEND_QUERY_HASHES", \* Transitions if "ACK" received and all WORKERS have received a key-share
               "SEND_KEY",          \* Transitions if "ACK" received and NOT all WORKERS have received a key-share, or upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "SEND_QUERY_HASHES",  \* SEND_QUERY_HASHES: Send message to query task hashes via TSC 
      end |-> {"RECV_QUERY_HASHES", \* Transitions upon sending "QUERY_HASHES" message
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "RECV_QUERY_HASHES",  \* RECV_QUERY_HASHES: Await list of hashes from TSC
      end |-> {"SEND_QUERY_DATA",   \* Transitions upon receiving "HASHES" with hash-list (length equal to numParticipants)
               "SEND_QUERY_HASHES", \* Transitions upon receiving "HASHES" with hash-list (length <numParticipants) or "INVALID"
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "SEND_QUERY_DATA",    \* SEND_QUERY_DATA: Send message to retrieve data from STORAGE 
      end |-> {"RECV_QUERY_DATA",   \* Transitions upon sending a "QUERY_DATA" message with hashes
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "RECV_QUERY_DATA",    \* RECV_QUERY_DATA: Await encrypted data from STORAGE
      end |-> {"EVALUATE",          \* Transitions upon receiving "DATA" with encrypted data
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "EVALUATE",           \* EVALUATE: Run CATD algorithm on requested data
      end |-> {"SEND_SUBMIT_EVAL",  \* Transitions upon completion of CATD algorithm
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "SEND_SUBMIT_EVAL",   \* SEND_SUBMIT_EVAL: Send message with evaluation results to TSC
      end |-> {"RECV_SUBMIT_EVAL",  \* Transitions upon sending "SUBMIT_EVAL" message
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "RECV_SUBMIT_EVAL",   \* RECV_SUBMIT_EVAL: Await acknowledgement of evaluation results from TSC
      end |-> {"SEND_WEIGHTS",      \* Transitions upon receiving "ACK" from TSC
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "SEND_WEIGHTS",       \* SEND_WEIGHTS: Send message with evaluation results to next WORKER
      end |-> {"RECV_WEIGHTS",      \* Transitions upon sending "WEIGHTS" message
               "SEND_KEY",          \* Transitions upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "RECV_WEIGHTS",       \* RECV_WEIGHTS: Await acknowledgement of evaluation results from WORKER
      end |-> {"SEND_WEIGHTS",      \* Transitions if "ACK" received and NOT all workers have received results
               "SEND_KEY",          \* Transitions if "ACK" received and all WORKERS have received results, or upon task timeout with remaining tasks
               "TERMINATED"}],      \* Transitions upon task timeout with no remaining tasks, or global timeout
      
   [start |-> "TERMINATED",         \* TERMINATED: No further operations possible
      end |-> {}]}                  \* Does not transition 
      
StateConsistency == 
    [][\A i \in 1..NumRequesters: 
        Requesters[i].state \in 
        {t.start : t \in AllowedStateTransitions}
    ]_Requesters
        
StateTransitions == 
    [][\A i \in 1..NumRequesters:
       LET t == CHOOSE x \in AllowedStateTransitions : x.start = Requesters[i].state 
       IN Requesters'[i].state \in (t.end \union {t.start})
    ]_Requesters
    
(***************************************************************************)
(*                             TYPE CONSISTENCY                            *)
(***************************************************************************)    
TypeOK == \A i \in 1..NumRequesters : LET r == Requesters[i] IN 
    /\ r.state \in {s.start : s \in AllowedStateTransitions}
    /\ r.pk = NULL \/ KeyOK(r.pk) 
    /\ r.sk = NULL \/ KeyOK(r.sk) 
    /\ \A t \in r.tasks : TaskOK(t)
    /\ r.currentTask = NULL \/ TaskOK(r.currentTask)
    /\ \A w \in r.unconfirmedWorkers : KeyOK(w)
    /\ \A w \in r.confirmedWorkers : KeyOK(w)
    /\ \A h \in r.submittedHashes : HashOK(h)
        
(***************************************************************************)
(*                                PROPERTIES                               *)
(***************************************************************************) 
TaskDeadlineUpdated == 
    \E r \in 1..NumRequesters : 
        LET after == IF Requesters[r]'.currentTask # NULL 
                     THEN Requesters[r]'.tasks \union {Requesters[r]'.currentTask}
                     ELSE Requesters[r]'.tasks
            before == IF Requesters[r].currentTask # NULL 
                      THEN Requesters[r].tasks \union {Requesters[r].currentTask}
                      ELSE Requesters[r].tasks
        IN \E t1 \in after : \A t2 \in before: 
            t1.taskId = t2.taskId =>
                \/ t1.Sd # t2.Sd
                \/ t1.Pd # t2.Pd
                \/ t1.Td # t2.Td 
               
MessageLost(i) ==
    /\ \E m \in Requesters[i].msgs : m \notin Requesters[i]'.msgs
    /\ LET removed == CHOOSE m \in Requesters[i].msgs : m \notin Requesters[i]'.msgs
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i]'.msgs \ {removed}]
       
(***************************************************************************)
(* LIVENESS: If a Requester progresses through/past the "SEND_KEY" or      *)
(* "SEND_WEIGHTS" states, which involve sending information to any Worker, *) 
(* then the Worker's message queue must contain 1 new message. (NOTE:      *)
(* Other properties verify that the necessary information is encrypted.)   *)
(***************************************************************************)
RequesterSendsKeysharesAndWeightsToWorkers == 
    [][\A i \in 1..NumRequesters: 
       IF /\ \/ /\ Requesters[i].state = "SEND_KEY"
                /\ Requesters'[i].state = "RECV_KEY" 
             \/ /\ Requesters[i].state = "SEND_WEIGHTS"
                /\ Requesters'[i].state = "RECV_WEIGHTS" 
          /\ ~TaskDeadlineUpdated
       THEN /\ \E j \in 1..NumWorkers : MessageAdded(Workers[j].msgs, Workers[j]'.msgs)
            /\ LET w == CHOOSE j \in 1..NumWorkers : MessageAdded(Workers[j].msgs, Workers[j]'.msgs)
               IN \E m \in Workers'[w].msgs : 
                    /\ m.type \in {"SEND_KEY", "WEIGHTS"}
                    /\ m.from = Requesters[i].pk
       ELSE TRUE
    ]_Requesters
    
(***************************************************************************)
(* LIVENESS: If a Requester progresses past any state that involves        *)
(* sending a message to TSC, then the TSC message queue must contain 1     *)
(* new message.                                                            *)
(***************************************************************************)
RequesterSendsMessagesToTSC == 
    [][\A i \in 1..NumRequesters:
       IF /\ Requesters[i].state \in {"SEND_POST_TASKS", "SEND_QUERY_TASKS", 
                                      "SEND_QUERY_HASHES", "SEND_SUBMIT_EVAL"}
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                            x.start = Requesters[i].state
             IN Requesters[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_KEY", allowedNextState.start}))
          /\ ~TaskDeadlineUpdated
       THEN Cardinality(TSCs'.msgs) = Cardinality(TSCs.msgs) + 1
       ELSE TRUE
    ]_Requesters
    
(***************************************************************************)
(* LIVENESS: If a Requester progresses past any state that involves        *)
(* sending a message to USC, then the USC message queue must contain 1     *)
(* new message.                                                            *)
(***************************************************************************)
RequesterSendsMessagesToUSC == 
    [][\A i \in 1..NumRequesters:
       IF /\ Requesters[i].state = "SEND_REGISTER"
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                            x.start = Requesters[i].state
             IN Requesters[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_KEY", allowedNextState.start}))
          /\ ~TaskDeadlineUpdated                
       THEN Cardinality(USCs'.msgs) = Cardinality(USCs.msgs) + 1
       ELSE TRUE
    ]_Requesters
    
(***************************************************************************)
(* LIVENESS: If a Requester progresses past any state that involves        *)
(* sending a message to STORAGE, then the STORAGE message queue must       *)
(* contain 1 new message.                                                  *)
(***************************************************************************)
RequesterSendsMessagesToStorage == 
    [][\A i \in 1..NumRequesters:
       IF /\ Requesters[i].state = "SEND_QUERY_DATA"
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                            x.start = Requesters[i].state
             IN Requesters[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_KEY", allowedNextState.start}))
          /\ ~TaskDeadlineUpdated                
       THEN /\ Cardinality(Storage'.msgs) = Cardinality(Storage.msgs) + 1
       ELSE TRUE
    ]_Workers

(***************************************************************************)
(* LIVENESS: If a Requester progresses past any state that involves        *)
(* receiving a message from Worker/TSC/USC/Storage, then the Requester     *)
(* must consume 1 message upon transitioning.                              *)
(***************************************************************************)    
RequesterConsumesMessagesToProgress == 
    [][\A i \in 1..NumRequesters:
       IF /\ Requesters[i].state \in
                {"RECV_REGISTER", "RECV_POST_TASKS","RECV_QUERY_TASKS", 
                 "RECV_KEY", "RECV_QUERY_HASHES", "RECV_QUERY_DATA",
                 "RECV_SUBMIT_EVAL", "RECV_WEIGHTS"}
          /\ LET match == (CHOOSE x \in AllowedStateTransitions : x.start = Requesters[i].state)
             IN Requesters[i]'.state \in (match.end \ ({"TERMINATED", match.start}))
          /\ ~TaskDeadlineUpdated             
       THEN Cardinality(Requesters[i]'.msgs) = Cardinality(Requesters[i].msgs) - 1
       ELSE TRUE
    ]_Requesters
    
(***************************************************************************)
(* LIVENESS: If a Requester is processing a "currentTask" for which the    *)
(* Submission/Proving deadline has passed, the Requester must proceed to   *)
(* next task (or terminate early) upon its next state update.              *)
(***************************************************************************)
RequesterTimeoutTaskIfDeadlinePassed == 
    [][\A i \in 1..NumRequesters:
       IF /\ Requesters[i].currentTask # NULL
          \* Condition 1a: Submission deadline passed before successful key distribution
          /\ \/ /\ Requesters[i].currentTask.Sd 
                /\ Requesters[i].state \in {"SEND_KEY", "RECV_KEY"}
             \* Condition 1b: Proving deadline passed before distribution of weights
             \/ /\ Requesters[i].currentTask.Pd
                /\ Requesters[i].state \in {"SEND_QUERY_HASHES", "RECV_QUERY_HASHES", 
                                            "SEND_QUERY_DATA", "RECV_QUERY_DATA", 
                                            "EVALUATE", "SEND_SUBMIT_EVAL", "RECV_SUBMIT_EVAL", 
                                            "SEND_WEIGHTS", "RECV_WEIGHTS"}
          \* Condition 2: Requester state must be updated
          /\ Requesters[i]'.state # Requesters[i].state
       THEN 
            \* Case 1: If Requester has another task, the current task should be updated
            \/ /\ Requesters[i].tasks # {}
               /\ Requesters[i]'.state = "SEND_KEY"
               /\ Requesters[i]'.currentTask = CHOOSE x \in Requesters[i].tasks :
                                               \A y \in Requesters[i].tasks: 
                                               x.taskId # y.taskId => x.taskId < y.taskId
            \* Case 2: If Requester has no additional tasks, it should terminate early
            \/ /\ Requesters[i].tasks = {}
               /\ Requesters[i]'.state = "TERMINATED"
               /\ Requesters[i]'.currentTask = NULL
            \* Case 3: Requester can crash at any point
            \/ Requesters[i]'.state = "TERMINATED"
       ELSE TRUE
    ]_Requesters

(***************************************************************************)    
(* SECURITY: If a Requester sends a private key-share to any Worker, then  *)
(* the key-share must be encrypted with the Worker's private key.          *)
(***************************************************************************)
IsKeyshareMessage(m, from) == 
    /\ m.type = "SEND_KEY" 
    /\ m.from = from 
    /\ "keyshare" \in DOMAIN m

RequesterSendsEncryptedKeyshares == 
    [][\A i \in 1..NumRequesters: 
        IF /\ Requesters[i].state = "SEND_KEY" 
           /\ Requesters'[i].state = "RECV_KEY" 
        THEN /\ \E j \in 1..NumWorkers : \E m \in Workers'[j].msgs :
                IsKeyshareMessage(m, Requesters[i].pk)
             /\ LET wid == CHOOSE j \in 1..NumWorkers: \E m \in Workers'[j].msgs: 
                                  IsKeyshareMessage(m, Requesters[i].pk)
                    msg == CHOOSE m \in Workers'[wid].msgs : 
                                  IsKeyshareMessage(m, Requesters[i].pk)
                IN /\ IsEncrypted(msg.keyshare)
                   /\ msg.keyshare.encryptionKey = Workers[wid].pk
                   /\ msg.keyshare.encryptedData.address = Requesters[i].sk.address
                   /\ msg.keyshare.encryptedData.type = "private_key"
                   /\ msg \notin Workers[wid].msgs
        ELSE TRUE
     ]_Requesters

(***************************************************************************)
(* SECURITY: When a Requester receives sensory data from Storage, all data *)
(* must be encrypted with a share of the Requester's public key.           *)
(***************************************************************************)
RequesterReceivesEncryptedSensoryData == 
    [][\A i \in 1..NumRequesters: 
        IF /\ Requesters[i].state = "RECV_QUERY_DATA"
           /\ Requesters'[i].state = "EVALUATE"
        THEN /\ \E m \in Requesters[i].msgs : m.type = "DATA" /\ m.from = Storage.pk
             /\ LET msg == CHOOSE m \in Requesters[i].msgs : m.type = "DATA" /\ m.from = Storage.pk
                IN /\ \A data \in msg.allData:
                        /\ data.address \in Requesters[i].currentTask.participants
                        /\ IsEncrypted(data.submission)
                        /\ data.submission.encryptionKey.address = Requesters[i].sk.address 
                        /\ data.submission.encryptionKey.type = "public_key" 
                        /\ "share" \in DOMAIN data.submission.encryptionKey
                   /\ msg \notin Requesters'[i].msgs
        ELSE TRUE
    ]_Requesters

(***************************************************************************)
(* TERMINATION: If a Requester receives a message with from USC with type  *)
(* "NOT_REGISTERED", it must terminate upon consuming the message and      *)
(* updating its state.                                                     *)
(***************************************************************************)
RequesterTerminatesIfNotRegistered == 
    [][\A i \in 1..NumRequesters:
       IF /\ \E msg \in Requesters[i].msgs : msg.type = "NOT_REGISTERED"
          /\ ~MessageLost(i) 
       THEN LET msg == CHOOSE m \in Requesters[i].msgs : m.type = "NOT_REGISTERED"
            IN IF msg \notin Requesters[i]'.msgs
               THEN Requesters[i]'.state = "TERMINATED"
               ELSE TRUE
       ELSE TRUE
    ]_Requesters

(***************************************************************************)
(*   TERMINATION: All Requesters terminate by conclusion of the process.   *)
(***************************************************************************)
Termination == 
    <>[](\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ RequesterTerminatesIfNotRegistered
    /\ RequesterSendsKeysharesAndWeightsToWorkers
    /\ RequesterSendsMessagesToTSC
    /\ RequesterSendsMessagesToUSC
    /\ RequesterSendsMessagesToStorage
    /\ RequesterConsumesMessagesToProgress
    /\ RequesterTimeoutTaskIfDeadlinePassed
    /\ RequesterSendsEncryptedKeyshares
    /\ RequesterReceivesEncryptedSensoryData
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Fri Mar 22 10:53:00 CET 2024 by jungc
\* Created Fri Mar 01 08:25:17 CET 2024 by jungc
