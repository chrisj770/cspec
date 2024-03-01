-------------------------------- MODULE USC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Common 

CONSTANT RegistrationDeadline

TypeOK == TRUE

Init == 
    USCs = [msgs |-> {},
              pk |-> [address |-> "USC", type |-> "public_key"],
           users |-> {}]

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
                            pk |-> [address |-> key, type |-> "public_key"], 
                            sk |-> [address |-> key, type |-> "private_key"]]
       IN USCs' = [USCs EXCEPT !.users = USCs.users \union {newUser},
                               !.msgs = USCs.msgs \ {msg}]
    
ReceiveRegister_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "userType"} : f \in DOMAIN msg
    /\ msg.type = "REGISTER"
    /\ msg.userType \in {"WORKER", "REQUESTER"}
    
ReceiveRegister_IsEnabled == 
    /\ \E msg \in USCs.msgs : ReceiveRegister_MessageFormat(msg)
    
ReceiveRegister == 
    /\ ReceiveRegister_IsEnabled
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveRegister_MessageFormat(m) 
       IN IF Time >= RegistrationDeadline
          THEN LET response == [type |-> "NOT_REGISTERED", from |-> USCs.pk] 
               IN /\ IF msg.userType = "WORKER"
                     THEN /\ Workers' = [Workers EXCEPT ![msg.from].msgs = Workers[msg.from].msgs \union {response}]
                          /\ UNCHANGED <<Requesters>>
                     ELSE /\ Requesters' = [Requesters EXCEPT ![msg.from].msgs = Requesters[msg.from].msgs \union {response}]
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
                        THEN /\ Workers' = [Workers EXCEPT ![msg.from].msgs = Workers[msg.from].msgs \union {response}]
                             /\ UNCHANGED <<Requesters>>
                        ELSE /\ Requesters' = [Requesters EXCEPT ![msg.from].msgs = Requesters[msg.from].msgs \union {response}]
                             /\ UNCHANGED <<Workers>> 
    /\ UNCHANGED <<TSCs>> 

(***************************************************************************)
(*                             GET_REPUTATION                              *)
(***************************************************************************) 
ReceiveGetReputation_MessageFormat(msg) == 
    /\ \A f \in {"from", "type", "user", "task"} : f \in DOMAIN msg
    /\ msg.from = TSCs.pk
    /\ msg.type = "GET_REPUTATION" 

ReceiveGetReputation_IsEnabled == 
    /\ \E msg \in USCs.msgs : ReceiveGetReputation_MessageFormat(msg)

ReceiveGetReputation == 
    /\ ReceiveGetReputation_IsEnabled 
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveGetReputation_MessageFormat(m)
           isRegistered == \/ IsRegistered(msg.user.address, "WORKER")
                           \/ IsRegistered(msg.user.address, "REQUESTER")
           user == IF ~isRegistered THEN NULL
                   ELSE CHOOSE u \in USCs.users : u.pk = msg.user
           response == [type |-> IF isRegistered THEN "REPUTATION" ELSE "NOT_REGISTERED",
                        from |-> USCs.pk,
                  reputation |-> IF isRegistered THEN user.reputation ELSE NULL, 
                        user |-> IF isRegistered THEN msg.user ELSE NULL, 
                        task |-> msg.task]
       IN /\ SendMessage(TSCs.pk, response)
          /\ USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, NextUnique>>
               
Next == 
    \/ ReceiveRegister
    \/ ReceiveGetReputation


=============================================================================
\* Modification History
\* Last modified Fri Mar 01 10:11:03 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
