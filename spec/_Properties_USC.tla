-------------------------- MODULE _Properties_USC --------------------------
EXTENDS USC, _Properties

(***************************************************************************)
(*                             STATE CONSISTENCY                           *)
(***************************************************************************)
AllowedStateTransitions == {
    [start |-> "WORKING",
       end |-> {}]
}

StateConsistency == 
    [][USCs.state \in {s.start : s \in AllowedStateTransitions}]_USCs
        
StateTransitions == 
    [][
        LET t == CHOOSE x \in AllowedStateTransitions : x.start = USCs.state 
        IN USCs'.state \in (t.end \union {t.start})
    ]_USCs
    
(***************************************************************************)
(*                             TYPE CONSISTENCY                            *)
(***************************************************************************)
UserOK(u) == 
    /\ \A f \in {"address", "reputation", "userType", "pk"} : f \in DOMAIN u
    /\ u.address \in {ToString(s) : s \in 0..NextUnique}
    /\ u.reputation \in Int
    /\ u.userType \in {"WORKER", "REQUESTER"}
    /\ KeyOK(u.pk)

TypeOK == 
    /\ USCs.state \in {s.start : s \in AllowedStateTransitions}
    /\ \A msg \in USCs.msgs : 
       \/ /\ \A f \in {"type", "from", "userType"} : f \in DOMAIN msg
          /\ msg.type = "REGISTER"
          /\ msg.from \in Int
          /\ msg.userType \in {"WORKER", "REQUESTER"}
       \/ MessageOK(msg)
    /\ KeyOK(USCs.pk)
    /\ \A user \in USCs.users : UserOK(user)
    /\ USCs.RegistrationDeadline \in {TRUE, FALSE}
    
(***************************************************************************)
(*                                PROPERTIES                               *)
(***************************************************************************)

(***************************************************************************)
(* LIVENESS: For all registered users, the assigned combination of address,*)
(* public key, and "userType" must be unique with respect to all other     *)
(* users (to prevent access conflicts or task-related malfunctions).       *)
(***************************************************************************)    
AllUsersUnique == 
    [][\A a \in USCs.users :
        LET match == {x \in USCs.users : x.address = a.address /\ x.pk = a.pk}
        IN Cardinality(match) = 1 
    ]_USCs

(***************************************************************************)
(* LIVENESS: After the "RegistrationDeadline" elapses, USC does not permit *) 
(* any additional registrations.                                           *)
(***************************************************************************)            
NoRegistrationsAfterDeadline == 
    [][USCs.RegistrationDeadline => 
       Cardinality(USCs'.users) = Cardinality(USCs.users)
    ]_USCs

(***************************************************************************)
(* TERMINATION: USC remains in "WORKING" state indefinitely by conclusion  *)
(* of the process.                                                         *)
(***************************************************************************)
Termination == 
    <>[](USCs.state = "WORKING")

Properties == 
    /\ AllUsersUnique 
    /\ NoRegistrationsAfterDeadline
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Thu Mar 21 08:28:21 CET 2024 by jungc
\* Created Wed Mar 13 10:00:37 CET 2024 by jungc
