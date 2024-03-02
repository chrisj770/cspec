----------------------- MODULE _Properties_Requester -----------------------
EXTENDS Requester

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
      
TypeOK ==
    \A r \in 1..NumRequesters : 
        /\ Requesters[r].state \in {s.start : s \in AllowedStateTransitions}

StateConsistency == 
    [](\A i \in 1..NumRequesters: 
        Requesters[i].state \in 
        {t.start : t \in AllowedStateTransitions})
        
StateTransitions == 
    [][\A i \in 1..NumRequesters:
       LET t == CHOOSE x \in AllowedStateTransitions : x.start = Requesters[i].state 
       IN Requesters'[i].state \in (t.end \union {t.start})
      ]_Requesters

Termination == 
    <>(\A r \in 1..NumRequesters: Requesters[r].state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Sat Mar 02 14:48:20 CET 2024 by jungc
\* Created Fri Mar 01 08:25:17 CET 2024 by jungc
