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
AllSubmittedDataIsEncrypted == 
    [][\A data \in Storage.data: IsEncrypted(data.submission)]_Storage

Termination == 
    <>[](USCs.state = "WORKING")

Properties == 
    /\ AllSubmittedDataIsEncrypted
    /\ Termination


=============================================================================
\* Modification History
\* Last modified Wed Mar 13 10:20:02 CET 2024 by jungc
\* Created Wed Mar 13 10:14:11 CET 2024 by jungc
