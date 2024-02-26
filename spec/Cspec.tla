------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANTS
    Tasks, 
    TaskPostDeadline, 
    RegistrationDeadline
    
vars == <<Workers, Requesters, USCs, TSCs, Time, NextPubkey, Storage>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
Blockchain == INSTANCE Blockchain
Database == INSTANCE Database

TypeOK == /\ Worker!TypeOK
          /\ Requester!TypeOK
          /\ Blockchain!TypeOK
          /\ Database!TypeOK
    
Init == /\ Worker!Init
        /\ Requester!Init
        /\ Blockchain!Init
        /\ Database!Init
        /\ Time = 0
        /\ NextPubkey = 1
        
Next == /\ \/ /\ \/ Worker!Next
                 \/ Requester!Next
              /\ UNCHANGED <<NextPubkey>>
           \/ /\ Blockchain!Next
              /\ UNCHANGED <<Storage>>
           \/ /\ Database!Next
              /\ UNCHANGED <<TSCs, USCs, NextPubkey>>
        /\ Time' = Time + 1

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------- *)
TSCMaximum == Cardinality(TSCs) <= NumRequesters * Cardinality(Tasks) 

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 10:01:21 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
