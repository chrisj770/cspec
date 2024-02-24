----------------------------- MODULE Blockchain -----------------------------
EXTENDS TSSC, TSC, USSC, USC

TypeOK == 
    /\ TSSCTypeOK
    /\ TSCTypeOK
    /\ USSCTypeOK
    /\ USCTypeOK

Init == 
    /\ TSSCInit
    /\ TSCInit
    /\ USSCInit
    /\ USCInit
    
Next == 
    \/ /\ TSCNext
       /\ UNCHANGED <<NextPubkey>>
    \/ TSSCNext
    \/ USSCNext

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:45:29 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
