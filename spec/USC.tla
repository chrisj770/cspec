-------------------------------- MODULE USC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Common 

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init == USCs = [msgs |-> {},
                  pk |-> [address |-> "USC", type |-> "public_key"],
               users |-> {},
               state |-> "WORKING", 
RegistrationDeadline |-> FALSE]

IsWorker(public_key) == 
    \E usc \in USCs.users: /\ usc.pk = public_key
                           /\ usc.userType = "WORKER"
                      
IsRequester(public_key) == 
    \E usc \in USCs.users: /\ usc.pk = public_key
                           /\ usc.userType = "REQUESTER"

(***************************************************************************)
(*                                REGISTER                                 *)
(***************************************************************************)    
IsRegistered(key, type) == 
    \E user \in USCs.users : /\ user.pk.address = key
                             /\ user.reputation # NULL
                             /\ user.userType = type
    
Register(key, msg) ==
    /\ ~IsRegistered(key, msg.userType)
    /\ LET newUser == [address |-> key, 
                    reputation |-> 1, 
                      userType |-> msg.userType,
                            pk |-> [address |-> key, type |-> "public_key"]]
       IN USCs' = [USCs EXCEPT !.users = USCs.users \union {newUser},
                               !.msgs = USCs.msgs \ {msg}]
    
ReceiveRegister_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "userType"} : f \in DOMAIN msg
    /\ msg.type = "REGISTER"
    /\ msg.userType \in {"WORKER", "REQUESTER"}
    
ReceiveRegister_IsEnabled == 
    /\ USCs.state = "WORKING"
    
ReceiveRegister == 
    /\ ReceiveRegister_IsEnabled
    /\ \E msg \in USCs.msgs : ReceiveRegister_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveRegister_MessageFormat(m) 
       IN IF USCs.RegistrationDeadline
          THEN LET response == [type |-> "NOT_REGISTERED", from |-> USCs.pk] 
               IN /\ IF msg.userType = "WORKER"
                     THEN /\ Workers' = [Workers EXCEPT ![msg.from].msgs = 
                                         Workers[msg.from].msgs \union {response}]
                          /\ UNCHANGED <<Requesters>>
                     ELSE /\ Requesters' = [Requesters EXCEPT ![msg.from].msgs = 
                                            Requesters[msg.from].msgs \union {response}]
                          /\ UNCHANGED <<Workers>>
                  /\ USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}] 
                  /\ UNCHANGED <<NextUnique>>
          ELSE LET newKey == ToString(NextUnique) 
               IN /\ Register(newKey, msg)
                  /\ NextUnique' = NextUnique + 1
                  /\ LET response == [type |-> "REGISTERED", 
                                      from |-> USCs.pk, 
                                       key |-> newKey, 
                                        pk |-> [address |-> newKey, type |-> "public_key"], 
                                        sk |-> [address |-> newKey, type |-> "private_key"]]
                     IN IF msg.userType = "WORKER"
                        THEN /\ Workers' = [Workers EXCEPT ![msg.from].msgs = 
                                            Workers[msg.from].msgs \union {response}]
                             /\ UNCHANGED <<Requesters>>
                        ELSE /\ Requesters' = [Requesters EXCEPT ![msg.from].msgs = 
                                               Requesters[msg.from].msgs \union {response}]
                             /\ UNCHANGED <<Workers>> 
    /\ UNCHANGED <<TSCs>> 

(***************************************************************************)
(*                             GET_REPUTATION                              *)
(***************************************************************************) 
GetReputation(user) == 
    LET usr == IF \/ IsRegistered(user.address, "WORKER")
                  \/ IsRegistered(user.address, "REQUESTER") 
               THEN CHOOSE u \in USCs.users : u.pk = user
               ELSE NULL
    IN usr.reputation
    
Terminating == /\ USCs.state = "WORKING"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 
               
Next == 
    \/ ReceiveRegister
    \/ Terminating


=============================================================================
\* Modification History
\* Last modified Wed Mar 13 10:20:43 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
