----------------------------- MODULE Blockchain -----------------------------
EXTENDS Common

CONSTANTS 
    TaskPostDeadline, 
    RegistrationDeadline
    
TSC == INSTANCE TSC
USC == INSTANCE USC

TypeOK == 
    /\ TSC!TypeOK
    /\ USC!TypeOK

Init == 
    /\ TSC!Init
    /\ USC!Init
    /\ NextPubkey = 1
    
Next == 
    \/ TSC!Next
    \/ USC!Next
   
=============================================================================
\* Modification History
\* Last modified Mon Feb 26 10:03:35 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
