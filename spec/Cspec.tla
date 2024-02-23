------------------------------- MODULE Cspec -------------------------------
EXTENDS USSC, USC, TSC, Common

CONSTANTS
    Tasks,
    TaskPostDeadline

vars == <<Workers, Requesters, USSC, USCs, TSSC, TSCs, Time, NextUserId>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
TSSCs == INSTANCE TSSC          

\* Note that TSSC extends USSC to call methods directly, so
\* we can't create an instance of USSC as done above.

TypeOK == /\ Worker!TypeOK
          /\ Requester!TypeOK
          /\ TSSCs!TypeOK
          /\ USSCTypeOK
    
Init == /\ Worker!Init
        /\ Requester!Init
        /\ TSSCs!Init
        /\ TSCInit
        /\ USSCInit 
        /\ USCInit
        /\ Time = 0
        
Next == /\ \/ /\ \/ Worker!Next
                 \/ Requester!Next
                 \/ TSSCs!Next
                 \/ TSCNext
              /\ UNCHANGED <<NextUserId>>
           \/ USSCNext
        /\ Time' = Time + 1

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Feb 23 15:34:23 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
