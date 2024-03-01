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
    
Next == 
    \/ TSC!Next
    \/ USC!Next
   
=============================================================================
\* Modification History
\* Last modified Fri Mar 01 10:11:28 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
