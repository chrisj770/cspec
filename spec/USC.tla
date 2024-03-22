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

(***************************************************************************)
(*                            HELPER OPERATORS                             *)
(***************************************************************************)
IsWorker(public_key) == 
    \E usc \in USCs.users: /\ usc.pk = public_key
                           /\ usc.userType = "WORKER"
                      
IsRequester(public_key) == 
    \E usc \in USCs.users: /\ usc.pk = public_key
                           /\ usc.userType = "REQUESTER"
    
IsRegistered(key, type) == 
    \E user \in USCs.users : /\ user.pk.address = key
                             /\ user.reputation # NULL
                             /\ user.userType = type

(***************************************************************************)
(*                                REGISTER                                 *)
(*                                                                         *)
(* Receive "REGISTER" message from Worker/Requester requesting to register *)
(* as their corresponding user-type. Upon receipt, perform an action based *)
(* on the following conditions:                                            *)
(*                                                                         *) 
(*  - If the "RegistrationDeadline" has not elapsed, generate a new        *) 
(*    public/private key-pair and persist all relevant information,        *)
(*    then send "REGISTERED" message to Worker/Requester containing        *) 
(*    the address and key-pair.                                            *)
(*                                                                         *)
(*  - If the "RegistrationDeadline has elapsed, send "NOT_REGISTERED"      *)
(*    message to Worker/Requester. (NOTE: This allows early termination    *)
(*    caused by failure to register.)                                      *)
(*                                                                         *)
(***************************************************************************)    
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
    
AcceptRegister(msg) == 
    LET newKey == ToString(NextUnique) 
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
        
RejectRegister(msg) == 
    LET response == [type |-> "NOT_REGISTERED", from |-> USCs.pk] 
    IN /\ IF msg.userType = "WORKER"
          THEN /\ Workers' = [Workers EXCEPT ![msg.from].msgs = 
                              Workers[msg.from].msgs \union {response}]
               /\ UNCHANGED <<Requesters>>
          ELSE /\ Requesters' = [Requesters EXCEPT ![msg.from].msgs = 
                                 Requesters[msg.from].msgs \union {response}]
               /\ UNCHANGED <<Workers>>
       /\ USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}] 
       /\ UNCHANGED <<NextUnique>>
    
ReceiveRegister == 
    /\ ReceiveRegister_IsEnabled
    /\ \E msg \in USCs.msgs : ReceiveRegister_MessageFormat(msg)
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveRegister_MessageFormat(m) 
       IN IF ~USCs.RegistrationDeadline
          THEN AcceptRegister(msg)
          ELSE RejectRegister(msg)
    /\ UNCHANGED <<TSCs>> 

(***************************************************************************)
(* GetReputation: This operator is invoked by the TSC to retrieve the      *)
(* reputation of a registered Worker or Requester.                         *)
(***************************************************************************) 
GetReputation(user) == 
    LET usr == IF \/ IsRegistered(user.address, "WORKER")
                  \/ IsRegistered(user.address, "REQUESTER") 
               THEN CHOOSE u \in USCs.users : u.pk = user
               ELSE NULL
    IN usr.reputation
    
(***************************************************************************)
(* Terminating: Allows the USC to remain working indefinitely, required by *)
(* TLA+ for stuttering.                                                    *)
(***************************************************************************)  
Terminating == /\ USCs.state = "WORKING"
               /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, Storage, NextUnique>> 

(***************************************************************************)
(*                            ACTION DEFINITIONS                           *)
(***************************************************************************)               
Next == 
    \/ ReceiveRegister
    \/ Terminating

=============================================================================
\* Modification History
\* Last modified Fri Mar 22 10:20:22 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
