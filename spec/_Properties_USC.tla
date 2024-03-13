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
Termination == 
    <>[](USCs.state = "WORKING")

Properties == 
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Wed Mar 13 10:25:25 CET 2024 by jungc
\* Created Wed Mar 13 10:00:37 CET 2024 by jungc
