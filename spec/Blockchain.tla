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
    /\ NextPubkey = 1
    
Next == 
    \/ /\ TSCNext
       /\ UNCHANGED <<NextPubkey>>
    \/ TSSCNext
    \/ USSCNext
   
=============================================================================
\* Modification History
\* Last modified Sun Feb 25 14:10:49 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
