------------------------ MODULE _Properties_Database ------------------------
EXTENDS Database, _Properties

(***************************************************************************)
(*                             STATE CONSISTENCY                           *)
(***************************************************************************)
AllowedStateTransitions == {
    [start |-> "WORKING",
       end |-> {}]
}

StateConsistency == 
    [][Storage.state \in {s.start : s \in AllowedStateTransitions}]_Storage
        
StateTransitions == 
    [][
        LET t == CHOOSE x \in AllowedStateTransitions : x.start = Storage.state 
        IN Storage'.state \in (t.end \union {t.start})
    ]_Storage
    
(***************************************************************************)
(*                             TYPE CONSISTENCY                            *)
(***************************************************************************)
DataOK(d) ==
    /\ \A f \in {"hash", "address", "submission"} : f \in DOMAIN d 
    /\ d.hash \in {ToString(s) : s \in 1..NextUnique}
    /\ KeyOK(d.address)

TypeOK == 
    /\ Storage.state \in {s.start : s \in AllowedStateTransitions}
    /\ \A msg \in Storage.msgs : MessageOK(msg)
    /\ KeyOK(Storage.pk)
    /\ \A data \in Storage.data : DataOK(data)
    
(***************************************************************************)
(*                                PROPERTIES                               *)
(***************************************************************************)

(***************************************************************************)
(* LIVENESS: If Storage receives a QUERY_DATA message from a Worker or     *)
(* Requester, then all addresses specified in "hashes" must already exist  *)
(* in the database.                                                        *)
(***************************************************************************)
StorageAllQueriedDataExists == 
    []( 
        (\E m \in Storage.msgs : m.type = "QUERY_DATA") => 
        LET msg == CHOOSE ms \in Storage.msgs : ms.type = "QUERY_DATA" 
        IN \A hash \in msg.hashes: \E d \in Storage.data : d.hash = hash
      )

(***************************************************************************)
(* LIVENESS: Throughout processing, the quantity of stored data never      *)
(* exceeds the expected maximum value: (#Workers x #Tasks)                 *)
(***************************************************************************)
StorageNeverExceedsMaximumSize == 
    [](Cardinality(Storage.data) <= NumWorkers * Len(Tasks))
    
(***************************************************************************)
(* SECURITY: All data received from Workers and persisted in the database  *)
(* must be encrypted via public key-share.                                 *)
(***************************************************************************)
StorageAllSubmittedDataIsEncrypted == 
    [](\A data \in Storage.data: IsEncrypted(data.submission))

(***************************************************************************)
(* TERMINATION: Storage remains in "WORKING" state indefinitely by         *)
(* conclusion of the process.                                              *)
(***************************************************************************)
Termination == 
    <>[](Storage.state = "WORKING")

Properties == 
    /\ StorageAllQueriedDataExists
    /\ StorageNeverExceedsMaximumSize
    /\ StorageAllSubmittedDataIsEncrypted
    /\ Termination


=============================================================================
\* Modification History
\* Last modified Thu Mar 21 08:05:54 CET 2024 by jungc
\* Created Wed Mar 13 10:14:11 CET 2024 by jungc
