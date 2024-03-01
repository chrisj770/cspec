------------------------- MODULE _Properties_Worker -------------------------
EXTENDS Worker

AllowedStateTransitions == {
   [start |-> "INIT",               \* INIT: Initialize local variables
      end |-> {"SEND_REGISTER"}],   \* Transitions upon completing initialization 
      
   [start |-> "SEND_REGISTER",      \* SEND_REGISTER: Attempt to register with USC
      end |-> {"RECV_REGISTER"}],   \* Transitions upon sending "REGISTER" message
      
   [start |-> "RECV_REGISTER",      \* RECV_REGISTER: Await registration information from USC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "REGISTERED" with key-share info
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED"
      
   [start |-> "SEND_QUERY_TASKS",   \* SEND_QUERY_TASKS: Send message to query tasks via TSC
      end |-> {"RECV_QUERY_TASKS"}],\* Transitions upon sending "QUERY_TASKS" message 
      
   [start |-> "RECV_QUERY_TASKS",   \* RECV_QUERY_TASKS: Await updated task information from TSC
      end |-> {"SEND_QUERY_TASKS",  \* Transitions upon receiving "INVALID"
               "SEND_CONFIRM_TASK", \* Transitions upon receiving "TASKS" with non-empty task list, 1+ w/ state "Available"
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED" or "TASKS" with empty task list
      
   [start |-> "SEND_CONFIRM_TASK",  \* SEND_CONFIRM_TASK: Send message confirm a specific task via TSC
      end |-> {"RECV_CONFIRM_TASK"}],\* Transitions upon sending "CONFIRM_TASK" message 
      
   [start |-> "RECV_CONFIRM_TASK",  \* RECV_CONFIRM_TASK: Await confirmation for specific task from TSC
      end |-> {"RECV_SEND_KEY",     \* Transitions upon receiving any response with 0 unconfirmed tasks remaining and 1+ successful confirmations
               "SEND_CONFIRM_TASK", \* Transitions upon receiving any response with 1+ unconfirmed tasks remaining
               "SEND_QUERY_TASK",   \* Transitions upon receiving "INVALID"
               "TERMINATED"}],      \* Transitions upon receiving "NOT_REGISTERED" 
      
   [start |-> "RECV_SEND_KEY",      \* RECV_SEND_KEY: Await key-share from REQUESTER
      end |-> {"COMPUTE",           \* Transitions upon receiving "SEND_KEY" message with key-share
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "COMPUTE",            \* COMPUTE: Generate sensory data locally
      end |-> {"SEND_SUBMIT_DATA",  \* Transitions upon successful generation of sensory data
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "SEND_SUBMIT_DATA",   \* SEND_SUBMIT_DATA: Send message with encrypted sensory data to STORAGE 
      end |-> {"RECV_SUBMIT_DATA",  \* Transitions upon sending "SUBMIT_DATA" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "RECV_SUBMIT_DATA",   \* RECV_SUBMIT_DATA: Await hash of sensory data from STORAGE
      end |-> {"SEND_SUBMIT_HASH",  \* Transitions upon receiving "HASH" from STORAGE with hash of sensory data
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "SEND_SUBMIT_HASH",   \* SEND_SUBMIT_HASH: Send message with sensory data hash to TSC
      end |-> {"RECV_SUBMIT_HASH",  \* Transitions upon sending "SUBMIT_HASH" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "RECV_SUBMIT_HASH",   \* RECV_SUBMIT_HASH: Await acknowledgment of data hash from TSC
      end |-> {"RECV_WEIGHTS",      \* Transitions upon receiving "ACK" from TSC
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "RECV_WEIGHTS",       \* RECV_WEIGHTS: Await set of evaluated worker weights from REQUESTER
      end |-> {"SEND_QUERY_DATA",   \* Transitions upon receiving "WEIGHTS" from REQUESTER with worker weights
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "SEND_QUERY_DATA",    \* SEND_QUERY_DATA: Send message to query STORAGE for submitted data
      end |-> {"RECV_QUERY_DATA",   \* Transitions upon sending "QUERY_DATA" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "RECV_QUERY_DATA",    \* RECV_QUERY_DATA: Await sensory data from STORAGE
      end |-> {"REQUEST_DATA",      \* Transitions upon receiving "DATA" from STORAGE with sensory data, with 1+ WORKERS remaining to verify
               "VERIFY",            \* Transitions upon receiving "DATA" from STORAGE with sensory data, with no WORKERS remaining to verify
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "REQUEST_DATA",       \* REQUEST_DATA: Send message to request sensory data from next WORKER, or respond to another WORKER by sending sensory data
      end |-> {"RECV_DATA",         \* Transitions upon sending "GET_DATA" message 
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks
      
   [start |-> "RECV_DATA",          \* RECV_DATA: Await sensory data from next WORKER, or respond to another WORKER by sending sensory data
      end |-> {"REQUEST_DATA",      \* Transitions upon receiving "DATA" from WORKER with 1+ workers remaining
               "VERIFY",            \* Transitions upon receiving "DATA" from WORKER with no workers remaining
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks

   [start |-> "VERIFY",             \* VERIFY: Run CATD algorithm on requested data and compare weights
      end |-> {"SEND_SUBMIT_EVAL",  \* Transitions upon completion of CATD algorithm and comparison
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks      
               
   [start |-> "SEND_SUBMIT_EVAL",   \* SEND_SUBMIT_EVAL: Send message with evaluation results to TSC
      end |-> {"RECV_SUBMIT_EVAL",  \* Transitions upon sending "SUBMIT_EVAL" message
               "RECV_SEND_KEY",     \* Transitions upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon task timeout with no remaining tasks           

   [start |-> "RECV_SUBMIT_EVAL",   \* RECV_SUBMIT_EVAL: Await acknowledgment of evaluation results from TSC
      end |-> {"RECV_SEND_KEY",     \* Transitions upon receiving "ACK" from TSC with remaining tasks, or upon task timeout with remaining tasks
               "SEND_QUERY_TASKS"}],\* Transitions upon receiving "ACK" from TSC with no remaining tasks, or upon task timeout with no remaining tasks  
      
   [start |-> "TERMINATED",         \* TERMINATED: No further operations possible
      end |-> {}]}                  \* Does not transition
      
StateConsistency == 
    [](\A i \in 1..NumWorkers: 
        Workers[i].state \in 
        {t.start : t \in AllowedStateTransitions})
        
StateTransitions == 
    [][\A i \in 1..NumWorkers:
       LET t == CHOOSE x \in AllowedStateTransitions : x.start = Workers[i].state 
       IN Workers'[i].state \in (t.end \union {t.start})
      ]_Workers
      
Termination == 
    <>(\A w \in 1..NumWorkers: Workers[w].state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions


=============================================================================
\* Modification History
\* Last modified Fri Mar 01 11:11:23 CET 2024 by jungc
\* Created Fri Mar 01 08:26:38 CET 2024 by jungc
