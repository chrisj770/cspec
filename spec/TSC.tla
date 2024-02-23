-------------------------------- MODULE TSC --------------------------------
EXTENDS FiniteSets, Sequences, Integers, Common 

TSCTypeOK == TRUE

TSCInit == TSCs = <<>>

TSCNext == \/ /\ Len(TSCs) = 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>>
           \/ /\ Len(TSCs) > 0
              /\ UNCHANGED <<Workers, Requesters, TSSC, TSCs, USSC, USCs>> \* TODO

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 14:49:20 CET 2024 by jungc
\* Created Thu Feb 22 14:17:45 CET 2024 by jungc
