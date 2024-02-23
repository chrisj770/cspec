-------------------------------- MODULE USSC --------------------------------
EXTENDS Sequences, USC, TLC, Common

CONSTANT RegistrationDeadline

USSCTypeOK == TRUE 

USSCInit == 
    /\ USSC = [msgs |-> <<>>]
    /\ NextUserId = 1

USSCReceiveRegister(msg) == \E usc \in 1..NumUSCs :
    /\ USCNotRegistered(usc)
    /\ NextUserId' = NextUserId + 1
    /\ LET newKey == ToString(NextUserId) IN
       /\ USCRegister(usc, newKey, msg.userType)
       /\ IF msg.userType = "WORKER" 
          THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \o 
                             <<[type |-> "REGISTERED", 
                               src |-> "USSC",  
                               pubkey |-> newKey]>>]
               /\ UNCHANGED <<Requesters, TSSC, TSCs>>
          ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \o 
                                <<[type |-> "REGISTERED", 
                                  src |-> "USSC",  
                                  pubkey |-> newKey]>>]
               /\ UNCHANGED <<Workers, TSSC, TSCs>>
            
USSCGetUser(pubkey, userType) == 
    \E usc \in 1..NumUSCs : USCIsRegistered(usc, pubkey, userType)
    
USSCReceive == 
    /\ Len(USSC.msgs) > 0
    /\ LET message == Head(USSC.msgs) IN
          USSCReceiveRegister(message)
    /\ USSC' = [USSC EXCEPT !.msgs = Tail(USSC.msgs)]
        
USSCNext == 
    \/ USSCReceive

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 15:51:04 CET 2024 by jungc
\* Created Thu Feb 22 10:07:57 CET 2024 by jungc
