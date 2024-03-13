---------------------------- MODULE _Properties ----------------------------
EXTENDS Common

(***************************************************************************)
(*              GLOBALLY-AVAILABLE CHECKS FOR TYPE CONSISTENCY             *)
(***************************************************************************)
KeyOK(k) == 
    /\ \A f \in {"address", "type"} : f \in DOMAIN k
    /\ \/ k.address \in {ToString(t) : t \in 0..NextUnique}
       \/ k.address \in {"TSC", "USC", "STORAGE"}
    /\ k.type \in {"public_key", "private_key"}
        
KeyshareOK(k) == 
    /\ KeyOK(k)
    /\ "share" \in DOMAIN k
    /\ k.share \in 0..NextUnique
    
WeightsOK(w) == 
    TRUE
   
WorkerTaskOK(t) == 
    /\ \A f \in {"taskId", "address", "category", "state", "owner", 
                 "numParticipants", "Sd", "Pd", "Td"} :
          f \in DOMAIN t
    /\ t.taskId \in 1..Len(Tasks)
    /\ t.address \in {ToString(a) : a \in 0..NextUnique}
    /\ t.category \in {"PlaceholderCategory"}
    /\ t.state \in {"Pending", "Available", "Unavailable", 
                    "QEvaluating", "Completed", "Canceled"}
    /\ KeyOK(t.owner)
    /\ t.numParticipants \in Int
    /\ t.Sd \in {TRUE, FALSE}
    /\ t.Pd \in {TRUE, FALSE}
    /\ t.Td \in {TRUE, FALSE}
       
TaskOK(t) == 
    /\ WorkerTaskOK(t)
    /\ \A f \in {"participants", "globalReputationThreshold", 
                 "expertiseReputationThreshold", "checkQ", "QEvaluate", 
                 "hashes", "requesterWeights", "workerWeights"} :
          f \in DOMAIN t
    /\ \A p \in t.participants : KeyOK(p)
    /\ t.globalReputationThreshold \in Int
    /\ t.expertiseReputationThreshold \in Int
    /\ \A h \in t.hashes : h \in {ToString(a) : a \in 0..NextUnique}
    /\ \/ t.requesterWeights = NULL 
       \/ WeightsOK(t.requesterWeights)
    /\ \A w \in t.workerWeights : WeightsOK(w)
    
MessageOK(msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ KeyOK(msg.from)
    
(***************************************************************************)
(*              GLOBALLY-AVAILABLE CHECKS FOR MESSAGE UPDATES              *)
(***************************************************************************)
MessageAdded(before, after) == 
    \E m \in after : m \notin before
    
MessageRemoved(before, after) == 
    \E m \in before : m \notin after

=============================================================================
\* Modification History
\* Last modified Wed Mar 13 10:36:38 CET 2024 by jungc
\* Created Sat Mar 02 14:49:49 CET 2024 by jungc
