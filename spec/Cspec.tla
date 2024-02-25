------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANTS
    Tasks,
    TaskPostDeadline, 
    RegistrationDeadline

vars == <<Workers, Requesters, USSC, USCs, TSSC, TSCs, Time, NextPubkey, Storage>>

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
              /\ UNCHANGED <<TSSC, TSCs, USSC, USCs, NextPubkey>>
        /\ Time' = Time + 1

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------- *)
TSCMaximum == Cardinality(TSCs) <= NumRequesters * Cardinality(Tasks) 

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 10:55:49 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
