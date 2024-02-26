-------------------------------- MODULE USSC --------------------------------
EXTENDS Sequences, USC, TLC, Common

CONSTANT RegistrationDeadline

USSCTypeOK == TRUE 

USSCInit == 
    /\ USSC = [msgs |-> {}]
    
USSCGetReputation(pubkey) == 
    LET u == CHOOSE i \in 1..NumUSCs : USCs[i].info.pubkey = pubkey 
    IN USCs[u].info.reputation
    
USSCReceiveRegister_MessageFormat(msg) == 
    /\ msg.type = "REGISTER"
    /\ msg.userType \in {"WORKER", "REQUESTER"}
    
USSCReceiveRegister_IsEnabled == 
    /\ Time < RegistrationDeadline
    /\ \E msg \in USSC.msgs : USSCReceiveRegister_MessageFormat(msg)
    
USSCReceiveRegister_CanRegister == 
    /\ \E usc \in 1..NumUSCs : USCNotRegistered(usc)
    
USSCReceiveRegister == 
    /\ USSCReceiveRegister_IsEnabled
    /\ LET msg == CHOOSE m \in USSC.msgs : USSCReceiveRegister_MessageFormat(m) 
       IN /\ IF ~USSCReceiveRegister_CanRegister
             THEN LET response == [type |-> "NOT_REGISTERED", src |-> "USSC"] 
                  IN IF msg.userType = "WORKER"
                     THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \union {response}]
                          /\ UNCHANGED <<Requesters, USCs>>
                     ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \union {response}]
                          /\ UNCHANGED <<Workers, USCs>>
             ELSE LET newKey == ToString(NextPubkey) 
                      usc == CHOOSE usc \in 1..NumUSCs : USCNotRegistered(usc) 
                      response == [type |-> "REGISTERED", src |-> "USSC", pubkey |-> newKey]
                  IN /\ USCRegister(usc, newKey, msg.userType)
                     /\ IF msg.userType = "WORKER"
                        THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \union {response}]
                             /\ UNCHANGED <<Requesters>>
                        ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \union {response}]
                             /\ UNCHANGED <<Workers>> 
                     /\ NextPubkey' = NextPubkey + 1
          /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \ {msg}]
    /\ UNCHANGED <<TSCs>> 
        
USSCNext == 
    \/ USSCReceiveRegister

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 08:43:03 CET 2024 by jungc
\* Created Thu Feb 22 10:07:57 CET 2024 by jungc
