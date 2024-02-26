-------------------------------- MODULE USC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Common 

CONSTANT RegistrationDeadline

TypeOK == TRUE

Init == 
    USCs = [msgs |-> {},
           users |-> {}]
                     
IsRegistered(key, type) == 
    \E user \in USCs.users : /\ user.address = key
                             /\ user.reputation # NULL
                             /\ user.userType = type
    
Register(key, msg) ==
    /\ ~IsRegistered(key, msg.userType)
    /\ LET newUser == [address |-> key, reputation |-> 1, userType |-> msg.userType]
       IN USCs' = [USCs EXCEPT !.users = USCs.users \union {newUser},
                               !.msgs = USCs.msgs \ {msg}]
    
ReceiveRegister_MessageFormat(msg) == 
    /\ msg.type = "REGISTER"
    /\ msg.userType \in {"WORKER", "REQUESTER"}
    
ReceiveRegister_IsEnabled == 
    /\ \E msg \in USCs.msgs : ReceiveRegister_MessageFormat(msg)
    
ReceiveRegister == 
    /\ ReceiveRegister_IsEnabled
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveRegister_MessageFormat(m) 
       IN IF Time >= RegistrationDeadline
          THEN LET response == [type |-> "NOT_REGISTERED", address |-> "USC"] 
               IN /\ IF msg.userType = "WORKER"
                     THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \union {response}]
                          /\ UNCHANGED <<Requesters>>
                     ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \union {response}]
                          /\ UNCHANGED <<Workers>>
                  /\ USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}] 
                  /\ UNCHANGED <<NextPubkey>>
          ELSE LET newKey == ToString(NextPubkey) 
               IN /\ Register(newKey, msg)
                  /\ NextPubkey' = NextPubkey + 1
                  /\ LET response == [type |-> "REGISTERED", 
                                   address |-> "USC", 
                                       key |-> newKey, 
                                        pk |-> [address |-> newKey, type |-> "public", share |-> NULL], 
                                        sk |-> [address |-> newKey, type |-> "private", share |-> NULL]]
                     IN IF msg.userType = "WORKER"
                        THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \union {response}]
                             /\ UNCHANGED <<Requesters>>
                        ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \union {response}]
                             /\ UNCHANGED <<Workers>> 
    /\ UNCHANGED <<TSCs>> 

ReceiveGetReputation_MessageFormat(msg) == 
    /\ msg.type = "GET_REPUTATION" 
    /\ msg.address = "TSC"
    /\ \A f \in {"user", "task"} : f \in DOMAIN msg

ReceiveGetReputation_IsEnabled == 
    /\ \E msg \in USCs.msgs : ReceiveGetReputation_MessageFormat(msg)

ReceiveGetReputation == 
    /\ ReceiveGetReputation_IsEnabled 
    /\ LET msg == CHOOSE m \in USCs.msgs : ReceiveGetReputation_MessageFormat(m)
           isRegistered == \/ IsRegistered(msg.user, "WORKER")
                           \/ IsRegistered(msg.user, "REQUESTER")
           user == IF ~isRegistered THEN NULL
                   ELSE CHOOSE u \in USCs.users : u.address = msg.user
           response == [type |-> IF isRegistered THEN "REPUTATION" ELSE "NOT_REGISTERED",
                       address |-> "USC",
                       reputation |-> IF isRegistered THEN user.reputation ELSE NULL, 
                       user |-> IF isRegistered THEN user.address ELSE NULL, 
                       task |-> msg.task]
       IN /\ SendMessage("TSC", response)
          /\ USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, NextPubkey>>
               
Next == 
    \/ ReceiveRegister
    \/ ReceiveGetReputation


=============================================================================
\* Modification History
\* Last modified Mon Feb 26 12:38:41 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
