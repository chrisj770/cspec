------------------------------- MODULE Cspec -------------------------------
EXTENDS Common

CONSTANTS
    Tasks,
    TaskPostDeadline, 
    RegistrationDeadline

vars == <<Workers, Requesters, USSC, USCs, TSSC, TSCs, Time, NextPubkey>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
Blockchain == INSTANCE Blockchain

TypeOK == /\ Worker!TypeOK
          /\ Requester!TypeOK
          /\ Blockchain!TypeOK
    
Init == /\ Worker!Init
        /\ Requester!Init
        /\ Blockchain!Init
        /\ Time = 0
        /\ NextPubkey = 1
        
Next == /\ \/ /\ \/ Worker!Next
                 \/ Requester!Next
              /\ UNCHANGED <<NextPubkey>>
           \/ Blockchain!Next
        /\ Time' = Time + 1

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------- *)

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:43:48 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
