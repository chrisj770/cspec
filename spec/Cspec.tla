------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANTS
    Tasks, 
    TaskPostDeadline, 
    TaskQueryDeadline,
    RegistrationDeadline

ASSUME /\ RegistrationDeadline < TaskPostDeadline
       /\ TaskPostDeadline < TaskQueryDeadline
    
vars == <<Workers, Requesters, USCs, TSCs, Time, NextUnique, Storage>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
Blockchain == INSTANCE Blockchain
Database == INSTANCE Database

RequesterProperties == INSTANCE _Properties_Requester
WorkerProperties == INSTANCE _Properties_Worker
TSCProperties == INSTANCE _Properties_TSC

TypeOK == /\ WorkerProperties!TypeOK
          /\ RequesterProperties!TypeOK
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
    
Terminated == 
    /\ \A i \in 1..NumWorkers : Workers[i].state = "TERMINATED"
    /\ \A j \in 1..NumRequesters : Requesters[j].state = "TERMINATED"
    /\ TSCs.state = "TERMINATED" 
    /\ USCs.state = "TERMINATED"
    /\ Storage.state = "TERMINATED"
        
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
    /\ TSCProperties!Properties

=============================================================================
\* Modification History
\* Last modified Sat Mar 02 14:49:04 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
