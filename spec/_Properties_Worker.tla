------------------------- MODULE _Properties_Worker -------------------------
EXTENDS Worker

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
      
   [start |-> "RECV_WEIGHTS",       \* RECV_WEIGHTS: Await set of evaluated worker weights from REQUESTER
      end |-> {"SEND_QUERY_DATA",   \* Transitions upon receiving "WEIGHTS" from REQUESTER with worker weights
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
      end |-> {"REQUEST_DATA",      \* Transitions upon receiving "DATA" from WORKER with 1+ workers remaining
               "VERIFY",            \* Transitions upon receiving "DATA" from WORKER with no workers remaining
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
      
TypeOK ==
    \A w \in 1..NumWorkers : 
        /\ Workers[w].state \in {s.start : s \in AllowedStateTransitions}
      
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

TerminatesIfNotRegistered == 
    [][\A i \in 1..NumWorkers:
       IF \E msg \in Workers[i].msgs : msg.type = "NOT_REGISTERED" 
       THEN LET msg == CHOOSE m \in Workers[i].msgs : m.type = "NOT_REGISTERED"
            IN IF msg \notin Workers[i]'.msgs
               THEN Workers[i]'.state = "TERMINATED"
               ELSE TRUE
       ELSE TRUE
    ]_Workers

SendsMessagesToUSC == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state = "SEND_REGISTER"
          /\ LET match == (CHOOSE x \in AllowedStateTransitions : x.start = "SEND_REGISTER")
             IN Workers[i]'.state \in (match.end \ ({"TERMINATED", "SEND_QUERY_TASKS", match.start}))
       THEN Cardinality(USCs'.msgs) = Cardinality(USCs.msgs) + 1
       ELSE TRUE
    ]_Workers
    
SendsMessagesToTSC == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state \in 
                {"SEND_QUERY_TASKS", "SEND_CONFIRM_TASK", "SEND_SUBMIT_HASH", "SEND_SUBMIT_EVAL"}
          /\ LET match == (CHOOSE x \in AllowedStateTransitions : x.start = Workers[i].state)
             IN Workers[i]'.state \in (match.end \ ({"TERMINATED", "SEND_QUERY_TASKS", match.start}))
       THEN Cardinality(TSCs'.msgs) = Cardinality(TSCs.msgs) + 1
       ELSE TRUE
    ]_Workers

SendsMessagesToStorage == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state \in {"SEND_QUERY_DATA", "SEND_SUBMIT_DATA"}
          /\ LET match == (CHOOSE x \in AllowedStateTransitions : x.start = Workers[i].state)
             IN Workers[i]'.state \in (match.end \ ({"TERMINATED", "SEND_QUERY_TASKS", match.start}))
       THEN /\ Cardinality(Storage'.msgs) = Cardinality(Storage.msgs) + 1
            /\ LET msg == CHOOSE m \in Storage'.msgs : m.from = Workers[i].pk
               IN \/ msg.type = "QUERY_DATA" 
                  \/ /\ msg.type = "SUBMIT_DATA" 
                     /\ IsEncrypted(msg.data)
       ELSE TRUE
    ]_Workers
    
SendsMessagesToWorkers == 
    [][\A i \in 1..NumWorkers:
       IF /\ Workers[i].state = "REQUEST_DATA"
          /\ LET match == (CHOOSE x \in AllowedStateTransitions : x.start = "REQUEST_DATA")
             IN Workers[i]'.state \in (match.end \ ({"TERMINATED", "SEND_QUERY_TASKS", match.start}))
       THEN \E j \in 1..NumWorkers : Cardinality(Workers[j]'.msgs) = Cardinality(Workers[j].msgs) + 1
       ELSE TRUE
    ]_Workers
    
Termination == 
    <>[](\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ TerminatesIfNotRegistered
    /\ SendsMessagesToUSC
    /\ SendsMessagesToTSC
    /\ SendsMessagesToStorage
    /\ SendsMessagesToWorkers
    /\ Termination


=============================================================================
\* Modification History
\* Last modified Sun Mar 03 11:02:52 CET 2024 by jungc
\* Created Fri Mar 01 08:26:38 CET 2024 by jungc
