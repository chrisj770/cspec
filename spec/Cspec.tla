------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANTS
    Tasks, 
    TaskPostDeadline, 
    TaskQueryDeadline,
    RegistrationDeadline, 
    MaxTime

ASSUME /\ RegistrationDeadline < TaskPostDeadline
       /\ TaskPostDeadline < TaskQueryDeadline
    
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
        
IncrementTimer == 
    Time' = IF Time < MaxTime THEN Time + 1 ELSE Time
        
Next == /\ \/ /\ \/ Worker!Next
                 \/ Requester!Next
              /\ UNCHANGED <<NextUnique>>
           \/ /\ Blockchain!Next
              /\ UNCHANGED <<Storage>>
           \/ /\ Database!Next
              /\ UNCHANGED <<TSCs, USCs>>
        /\ IncrementTimer

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Properties == 
    /\ RequesterProperties!Properties
    /\ WorkerProperties!Properties

=============================================================================
\* Modification History
\* Last modified Fri Mar 01 15:53:26 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
