------------------------------- MODULE Cspec -------------------------------
EXTENDS Worker, Requester, USSC, USC, TSSC, TSC, Common

vars == <<Workers, Requesters, USSC, USCs, TSSC, TSCs>>

TypeOK == /\ WorkerTypeOK
          /\ RequesterTypeOK
          /\ TSSCTypeOK
          /\ USSCTypeOK
    
Init == /\ WorkerInit
        /\ RequesterInit
        /\ USSCInit 
        /\ USCInit
        /\ TSSCInit
        /\ TSCInit
        
Next == \/ WorkerNext
        \/ RequesterNext
        \/ USSCNext

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Thu Feb 22 16:19:37 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
