------------------------- MODULE _Properties_Worker -------------------------
EXTENDS Worker, _Properties

(***************************************************************************)
(*                             STATE CONSISTENCY                           *)
(***************************************************************************)
AllowedStateTransitions == {
   [start |-> "INIT",               \* INIT: Initialize local variables
      end |-> {"SEND_REGISTER",     \* Transitions upon completing initialization
               "TERMINATED"}],      \* Transitions upon global timeout 
      
   [start |-> "SEND_REGISTER",      \* SEND_REGISTER: Attempt to register with USC
      end |-> {"RECV_REGISTER",     \* Transitions upon sending "REGISTER" message
               "TERMINATED"}],      \* Transitions upon TaskQueryDeadline elapsing, or global timeout
      
   [start |-> "RECV_REGISTER",      \* RECV_REGISTER: Await registration information from USC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "REGISTERED" with key-share info
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED", or global timeout
      
   [start |-> "SEND_QUERY_TASKS",   \* SEND_QUERY_TASKS: Send message to query tasks via TSC
      end |-> {"RECV_QUERY_TASKS",  \* Transitions upon sending "QUERY_TASKS" message 
               "TERMINATED"}],      \* Transitions upon TaskQueryDeadline elapsing, or global timeout
        
   [start |-> "RECV_QUERY_TASKS",   \* RECV_QUERY_TASKS: Await updated task information from TSC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "INVALID"
               "SEND_CONFIRM_TASK", \* Transitions upon receiving "TASKS" with non-empty task list, 1+ w/ state "Available"
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED" or "TASKS" with empty task list, or TaskQueryDeadline elapsing, or global timeout
      
   [start |-> "SEND_CONFIRM_TASK",  \* SEND_CONFIRM_TASK: Send message confirm a specific task via TSC
      end |-> {"RECV_CONFIRM_TASK", \* Transitions upon sending "CONFIRM_TASK" message 
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_CONFIRM_TASK",  \* RECV_CONFIRM_TASK: Await confirmation for specific task from TSC
      end |-> {"RECV_SEND_KEY",     \* Transitions upon receiving any response with 0 unconfirmed tasks remaining and 1+ successful confirmations
               "SEND_CONFIRM_TASK", \* Transitions upon receiving any response with 1+ unconfirmed tasks remaining
               "SEND_QUERY_TASKS",  \* Transitions upon receiving "INVALID"
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED", or global timeout 
      
   [start |-> "RECV_SEND_KEY",      \* RECV_SEND_KEY: Await key-share from REQUESTER
      end |-> {"COMPUTE",           \* Transitions upon receiving "SEND_KEY" message with key-share
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "COMPUTE",            \* COMPUTE: Generate sensory data locally
      end |-> {"SEND_SUBMIT_DATA",  \* Transitions upon successful generation of sensory data
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "SEND_SUBMIT_DATA",   \* SEND_SUBMIT_DATA: Send message with encrypted sensory data to STORAGE 
      end |-> {"RECV_SUBMIT_DATA",  \* Transitions upon sending "SUBMIT_DATA" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_SUBMIT_DATA",   \* RECV_SUBMIT_DATA: Await hash of sensory data from STORAGE
      end |-> {"SEND_SUBMIT_HASH",  \* Transitions upon receiving "HASH" from STORAGE with hash of sensory data
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "SEND_SUBMIT_HASH",   \* SEND_SUBMIT_HASH: Send message with sensory data hash to TSC
      end |-> {"RECV_SUBMIT_HASH",  \* Transitions upon sending "SUBMIT_HASH" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_SUBMIT_HASH",   \* RECV_SUBMIT_HASH: Await acknowledgment of data hash from TSC
      end |-> {"RECV_WEIGHTS",      \* Transitions upon receiving "ACK" from TSC
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_WEIGHTS",       \* RECV_WEIGHTS: Await set of evaluated Worker weights from REQUESTER
      end |-> {"SEND_QUERY_DATA",   \* Transitions upon receiving "WEIGHTS" from REQUESTER with Worker weights
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "SEND_QUERY_DATA",    \* SEND_QUERY_DATA: Send message to query STORAGE for submitted data
      end |-> {"RECV_QUERY_DATA",   \* Transitions upon sending "QUERY_DATA" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_QUERY_DATA",    \* RECV_QUERY_DATA: Await sensory data from STORAGE
      end |-> {"REQUEST_DATA",      \* Transitions upon receiving "DATA" from STORAGE with sensory data, with 1+ WORKERS remaining to verify
               "VERIFY",            \* Transitions upon receiving "DATA" from STORAGE with sensory data, with no WORKERS remaining to verify
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "REQUEST_DATA",       \* REQUEST_DATA: Send message to request sensory data from next WORKER, or respond to another WORKER by sending sensory data
      end |-> {"RECV_DATA",         \* Transitions upon sending "GET_DATA" message 
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout
      
   [start |-> "RECV_DATA",          \* RECV_DATA: Await sensory data from next WORKER, or respond to another WORKER by sending sensory data
      end |-> {"REQUEST_DATA",      \* Transitions upon receiving "DATA" from WORKER with 1+ Workers remaining
               "VERIFY",            \* Transitions upon receiving "DATA" from WORKER with no Workers remaining
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout

   [start |-> "VERIFY",             \* VERIFY: Run CATD algorithm on requested data and compare weights
      end |-> {"SEND_SUBMIT_EVAL",  \* Transitions upon completion of CATD algorithm and comparison
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout      
               
   [start |-> "SEND_SUBMIT_EVAL",   \* SEND_SUBMIT_EVAL: Send message with evaluation results to TSC
      end |-> {"RECV_SUBMIT_EVAL",  \* Transitions upon sending "SUBMIT_EVAL" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout           

   [start |-> "RECV_SUBMIT_EVAL",   \* RECV_SUBMIT_EVAL: Await acknowledgment of evaluation results from TSC
      end |-> {"RECV_SEND_KEY",     \* Transitions upon receiving "ACK" from TSC with remaining tasks, or upon task timeout with remaining tasks
               "SEND_QUERY_TASKS",  \* Transitions upon receiving "ACK" from TSC with no remaining tasks, or upon task timeout with no remaining tasks
               "TERMINATED"}],      \* Transitions upon global timeout  
      
   [start |-> "TERMINATED",         \* TERMINATED: No further operations possible
      end |-> {}]}                  \* Does not transition
      
StateConsistency == 
    [][\A i \in 1..NumWorkers: 
        Workers[i].state \in 
        {t.start : t \in AllowedStateTransitions}
    ]_Workers
    
StateTransitions == 
    [][\A i \in 1..NumWorkers:
       LET t == CHOOSE x \in AllowedStateTransitions : x.start = Workers[i].state 
       IN Workers'[i].state \in (t.end \union {t.start})
    ]_Workers

(***************************************************************************)
(*                             TYPE CONSISTENCY                            *)
(***************************************************************************)
TypeOK == \A i \in 1..NumWorkers : LET w == Workers[i] IN
    /\ w.state \in {s.start : s \in AllowedStateTransitions}
    /\ w.pk = NULL \/ KeyOK(w.pk)
    /\ w.sk = NULL \/ KeyOK(w.sk)
    /\ w.requesterSk = NULL \/ KeyshareOK(w.requesterSk)
    /\ \A t \in w.pendingTasks : WorkerTaskOK(t)
    /\ \A t \in w.confirmedTasks : WorkerTaskOK(t)
    /\ \A t \in w.unconfirmedTasks : WorkerTaskOK(t)
    /\ w.currentConfirmTask = NULL \/ WorkerTaskOK(w.currentConfirmTask) 
    /\ w.currentTask = NULL \/ WorkerTaskOK(w.currentTask) 
    /\ w.currentHash = NULL \/ HashOK(w.currentHash)
    /\ \A p \in w.participantsSent : KeyOK(p) 
    /\ \A p \in w.participantsRcvd : KeyOK(p)
    /\ w.TaskQueryDeadline \in {TRUE, FALSE}  
    
(***************************************************************************)
(*                                PROPERTIES                               *)
(***************************************************************************)
TaskQueryDeadlineUpdated(i) == 
    Workers[i]'.TaskQueryDeadline # Workers[i].TaskQueryDeadline 
    
TaskDeadlineUpdated(i) == 
    LET beforeTasks == (Workers[i].unconfirmedTasks \union 
                        Workers[i].confirmedTasks \union
                        Workers[i].pendingTasks)
        before == IF Workers[i].currentTask # NULL
                  THEN beforeTasks \union {Workers[i].currentTask}
                  ELSE beforeTasks
        afterTasks == (Workers[i]'.unconfirmedTasks \union 
                       Workers[i]'.confirmedTasks \union
                       Workers[i]'.pendingTasks)
        after == IF Workers[i]'.currentTask # NULL
                 THEN afterTasks \union {Workers[i]'.currentTask}
                 ELSE afterTasks
    IN \E t \in before : \A u \in after :
       t.taskId = u.taskId => 
        \/ t.Sd # u.Sd
        \/ t.Pd # u.Pd
        \/ t.Td # u.Pd 
        
MessageLost(i) ==
    /\ \E m \in Workers[i].msgs : m \notin Workers[i]'.msgs
    /\ LET removed == CHOOSE m \in Workers[i].msgs : m \notin Workers[i]'.msgs
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i]'.msgs \ {removed}]
        
(***************************************************************************)
(* LIVENESS: If a Worker progresses past any state that involves sending a *)
(* message to TSC, then the TSC message queue must contain 1 new message.  *)
(***************************************************************************)
WorkerSendsMessagesToTSC == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state \in {"SEND_QUERY_TASKS", "SEND_CONFIRM_TASK", 
                                   "SEND_SUBMIT_HASH", "SEND_SUBMIT_EVAL"}
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                            x.start = Workers[i].state
             IN Workers[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_QUERY_TASKS", allowedNextState.start}))
       THEN Cardinality(TSCs'.msgs) = Cardinality(TSCs.msgs) + 1
       ELSE TRUE
    ]_Workers
    
(***************************************************************************)
(* LIVENESS: If a Worker progresses past any state that involves sending a *)
(* message to USC, then the USC message queue must contain 1 new message.  *)
(***************************************************************************)
WorkerSendsMessagesToUSC == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state = "SEND_REGISTER"
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                            x.start = Workers[i].state
             IN Workers[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_QUERY_TASKS", allowedNextState.start}))
       THEN Cardinality(USCs'.msgs) = Cardinality(USCs.msgs) + 1
       ELSE TRUE
    ]_Workers

(***************************************************************************)
(* LIVENESS: If a Worker progresses past any state that involves sending a *)
(* message to STORAGE, then the STORAGE message queue must contain 1 new   *)
(* message. Additionally, if the message has type "SUBMIT_DATA", it must   *)
(* contain encrypted data that cannot be viewed by external actors.        *)
(***************************************************************************)
WorkerSendsMessagesToStorage == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state \in {"SEND_QUERY_DATA", "SEND_SUBMIT_DATA"}
          /\ LET allowedNextState == CHOOSE x \in AllowedStateTransitions : 
                                         x.start = Workers[i].state
             IN Workers[i]'.state \in (allowedNextState.end \ 
                ({"TERMINATED", "SEND_QUERY_TASKS", allowedNextState.start}))
       THEN /\ Cardinality(Storage'.msgs) = Cardinality(Storage.msgs) + 1
            /\ LET msg == CHOOSE m \in Storage'.msgs : m.from = Workers[i].pk
               IN \/ msg.type = "QUERY_DATA" 
                  \/ /\ msg.type = "SUBMIT_DATA" 
                     /\ IsEncrypted(msg.data)
       ELSE TRUE
    ]_Workers

(***************************************************************************)    
(* LIVENESS: If a Worker progresses to the VERIFY state, then both of the  *) 
(* following conditions must be fulfilled:                                 *)
(*                                                                         *) 
(*  (1) Worker has received a quantity of sensory data equal to the        *)
(*      total number of Workers in its "currentTask" (minus one),          *)
(*      Additionally, the list "participantsRcvd" must be empty.           *)
(*                                                                         *)
(*  (2) All other Workers have either (a) received sensory data from       *)
(*      the Worker, or (b) received a message containing sensory data      *)
(*      from the Worker. Additionally, the list "participantsSent"         *) 
(*      must be empty.                                                     *)
(*                                                                         *)
(***************************************************************************)
WorkerCompletesSensoryDataExchange == 
    [][\A i \in 1..NumWorkers: 
        IF /\ Workers[i].state \in {"REQUEST_DATA", "RECV_DATA"}
           /\ Workers'[i].state = "VERIFY"
        THEN /\ Cardinality(Workers[i].submittedData) = Workers[i].currentTask.numParticipants - 1
             /\ Cardinality(Workers[i].participantsRcvd) = 0
             /\ \A j \in 1..NumWorkers : Workers[j].pk \in Workers[i].currentTask.participants => 
                \/ LET work == CHOOSE w \in Workers[i].submittedData : w.address = Workers[i].pk
                   IN work \in Workers[j].submittedData
                \/ /\ \E m \in Workers[j].msgs : 
                        /\ m.from = Workers[i].pk
                        /\ m.type = "DATA"
                        /\ Workers[i].pk = m.data.address
             /\ Cardinality(Workers[i].participantsSent) = 0
        ELSE TRUE
    ]_Workers

(***************************************************************************)
(* LIVENESS: If a Worker is processing a "currentTask" for which the       *)
(* Submission/Proving deadline has passed, the Worker must proceed to the  *)
(* next task (or re-query tasks) upon its next state update.               *)
(***************************************************************************)
WorkerTimeoutTaskIfDeadlinePassed == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].currentTask # NULL
          \* Condition 1a: Submission deadline passed before submission of data hash
          /\ \/ /\ Workers[i].currentTask.Sd 
                /\ Workers[i].state \in {"RECV_SEND_KEY", "COMPUTE", "SEND_SUBMIT_DATA", 
                                         "RECV_SUBMIT_DATA", "SEND_SUBMIT_HASH",
                                         "RECV_SUBMIT_HASH"}
             \* Condition 1b: Proving deadline passed before submission of evaluation
             \/ /\ Workers[i].currentTask.Pd
                /\ Workers[i].state \in {"RECV_WEIGHTS", "SEND_QUERY_DATA", "RECV_QUERY_DATA", 
                                         "REQUEST_DATA", "RECV_DATA", "VERIFY", 
                                         "SEND_SUBMIT_EVAL", "RECV_SUBMIT_EVAL"}
          \* Condition 2: Worker state must be updated
          /\ Workers[i]'.state # Workers[i].state
       THEN 
            \* Case 1: If Worker has another task, the current task should be incremented
            \/ /\ Workers[i].confirmedTasks # {}
               /\ Workers[i]'.state = "RECV_SEND_KEY"
               /\ Workers[i]'.currentTask = CHOOSE x \in Workers[i].confirmedTasks :
                                            \A y \in Workers[i].confirmedTasks: 
                                            x.taskId # y.taskId => x.taskId < y.taskId
            \* Case 2: If Worker has no additional tasks, it should re-query TSC for tasks
            \/ /\ Workers[i].confirmedTasks = {}
               /\ Workers[i]'.state = "SEND_QUERY_TASKS"
               /\ Workers[i]'.currentTask = NULL
            \* Case 3: Worker can crash at any point
            \/ Workers[i]'.state = "TERMINATED"
       ELSE TRUE
    ]_Workers
    
(***************************************************************************)
(* SECURITY: During key distribution, if a Worker receives a message from  *)
(* a Requester containing a keyshare, the contents must be encrypted with  *)
(* a public key for which ONLY the Worker's private key can be used for    *)
(* decryption.                                                             *)
(***************************************************************************)
WorkerReceivesEncryptedKeyshares == 
    [][\A i \in 1..NumWorkers : 
       IF /\ Workers[i].currentTask # NULL
          /\ Workers[i].state = "RECV_SEND_KEY"
          /\ \E m \in Workers[i].msgs : /\ m.from = Workers[i].currentTask.owner
                                        /\ m.type = "SEND_KEY"
       THEN 
            LET msg == CHOOSE m \in Workers[i].msgs : 
                        /\ m.from = Workers[i].currentTask.owner
                        /\ m.type = "SEND_KEY"
            IN /\ IsEncrypted(msg.keyshare)
               /\ msg.keyshare.encryptionKey.address = Workers[i].pk.address
               /\ msg.keyshare.encryptionKey.type = Workers[i].pk.type
       ELSE TRUE
    ]_Workers

(***************************************************************************)
(* SECURITY: During sensory data submission, every message sent to STORAGE *)
(* must contain encrypted data for which the Requester's public key was    *)
(* used for encryption, corresponding to the private key "share" received. *)
(***************************************************************************)
WorkerSendsEncryptedSensoryData ==
    [][\A i \in 1..NumWorkers : 
       IF /\ Workers[i].currentTask # NULL
          /\ Workers[i].state = "SEND_SUBMIT_DATA"
          /\ Workers[i]'.state = "RECV_SUBMIT_DATA"
          /\ MessageAdded(Storage.msgs, Storage'.msgs)
       THEN 
            LET msg == CHOOSE m \in Storage'.msgs : 
                       /\ m.from = Workers[i].pk
                       /\ m.type = "SUBMIT_DATA"
            IN /\ IsEncrypted(msg.data) 
               /\ msg.data.encryptionKey.address = Workers[i].requesterSk.address
               /\ msg.data.encryptionKey.type = "public_key" 
               /\ msg.data.encryptionKey.share = Workers[i].requesterSk.share
       ELSE TRUE
    ]_Workers

(***************************************************************************)
(* TERMINATION: If a Worker receives a message with type "NOT_REGISTERED", *)
(* it must terminate upon consuming the message and updating its state.    *)
(***************************************************************************)
WorkerTerminatesIfNotRegistered == 
    [][\A i \in 1..NumWorkers:
       IF /\ \E msg \in Workers[i].msgs : msg.type = "NOT_REGISTERED"
          /\ ~MessageLost(i) 
       THEN LET msg == CHOOSE m \in Workers[i].msgs : m.type = "NOT_REGISTERED"
            IN IF msg \notin Workers[i]'.msgs
               THEN Workers[i]'.state = "TERMINATED"
               ELSE TRUE
       ELSE TRUE
    ]_Workers

(***************************************************************************)
(*  TERMINATION: All Workers must terminate by conclusion of the process.  *)
(***************************************************************************)
Termination == 
    <>[](\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ WorkerSendsMessagesToTSC
    /\ WorkerSendsMessagesToUSC
    /\ WorkerSendsMessagesToStorage
    /\ WorkerCompletesSensoryDataExchange
    /\ WorkerTimeoutTaskIfDeadlinePassed
    /\ WorkerReceivesEncryptedKeyshares
    /\ WorkerSendsEncryptedSensoryData
    /\ WorkerTerminatesIfNotRegistered
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Fri Mar 22 10:16:48 CET 2024 by jungc
\* Created Fri Mar 01 08:26:38 CET 2024 by jungc
