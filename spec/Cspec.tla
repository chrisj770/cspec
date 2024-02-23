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
        \/ TSSCNext
        \/ TSCNext

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Feb 23 10:04:11 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
