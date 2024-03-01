------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANTS
    Tasks, 
    TaskPostDeadline, 
    RegistrationDeadline
    
vars == <<Workers, Requesters, USCs, TSCs, Time, NextUnique, Storage>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
Blockchain == INSTANCE Blockchain
Database == INSTANCE Database

RequesterProperties == INSTANCE _Properties_Requester
WorkerProperties == INSTANCE _Properties_Worker

TypeOK == /\ Worker!TypeOK
          /\ Requester!TypeOK
          /\ Blockchain!TypeOK
          /\ Database!TypeOK
    
Init == /\ Worker!Init
        /\ Requester!Init
        /\ Blockchain!Init
        /\ Database!Init
        /\ Time = 0
        /\ NextUnique = 1
        
Next == /\ \/ /\ \/ Worker!Next
                 \/ Requester!Next
              /\ UNCHANGED <<NextUnique>>
           \/ /\ Blockchain!Next
              /\ UNCHANGED <<Storage>>
           \/ /\ Database!Next
              /\ UNCHANGED <<TSCs, USCs>>
        /\ Time' = Time + 1

Spec == Init /\ [][Next]_vars

Properties == 
    /\ RequesterProperties!Properties
    /\ WorkerProperties!Properties

=============================================================================
\* Modification History
\* Last modified Fri Mar 01 10:11:57 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
