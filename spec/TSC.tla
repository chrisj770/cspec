-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, Common 

TSCTypeOK == TRUE

TSCInit == TSCs = <<>>

TSCNext == UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 10:05:01 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
