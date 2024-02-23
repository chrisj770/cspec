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
    \/ /\ \/ TSSCNext
          \/ TSCNext
       /\ UNCHANGED <<NextUserId>>
    \/ USSCNext

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 15:42:11 CET 2024 by jungc
\* Created Fri Feb 23 15:36:50 CET 2024 by jungc
