----------------------------- MODULE Blockchain -----------------------------
EXTENDS  USSC, USC

CONSTANTS 
    TaskPostDeadline
    
TSC == INSTANCE TSC

TypeOK == 
    /\ TSC!TypeOK
    /\ USSCTypeOK
    /\ USCTypeOK

Init == 
    /\ TSC!Init
    /\ USSCInit
    /\ USCInit
    /\ NextPubkey = 1
    
Next == 
    \/ TSC!Next
    \/ USSCNext
   
=============================================================================
\* Modification History
\* Last modified Mon Feb 26 08:36:29 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
