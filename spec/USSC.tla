-------------------------------- MODULE USSC --------------------------------
EXTENDS Sequences, USC, TLC, Common

CONSTANT RegistrationDeadline

USSCTypeOK == TRUE 

USSCInit == 
    /\ USSC = [msgs |-> <<>>]
    /\ NextPubkey = 1

USSCReceiveRegister(msg) == \E usc \in 1..NumUSCs :
    /\ USCNotRegistered(usc)
    /\ NextPubkey' = NextPubkey + 1
    /\ LET newKey == ToString(NextPubkey) IN
       /\ USCRegister(usc, newKey, msg.userType)
       /\ IF msg.userType = "WORKER" 
          THEN /\ Len(Workers[msg.src].msgs) = 0
               /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \o 
                             <<[type |-> "REGISTERED", 
                               src |-> "USSC",  
                               pubkey |-> newKey]>>]
               /\ UNCHANGED <<Requesters, TSSC, TSCs>>
          ELSE /\ Len(Requesters[msg.src].msgs) = 0
               /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \o 
                                <<[type |-> "REGISTERED", 
                                  src |-> "USSC",  
                                  pubkey |-> newKey]>>]
               /\ UNCHANGED <<Workers, TSSC, TSCs>>
            
USSCCheckUser(pubkey, userType) == 
    \E usc \in 1..NumUSCs : USCIsRegistered(usc, pubkey, userType)
    
USSCGetUser(pubkey, userType) == 
    LET i == CHOOSE j \in 1..NumUSCs :
                /\ USCs[j].info.pubkey = pubkey
                /\ USCs[j].info.userType = userType 
    IN USCs[i]
    
USSCReceive == 
    /\ Len(USSC.msgs) > 0
    /\ LET message == Head(USSC.msgs) IN
          USSCReceiveRegister(message)
    /\ USSC' = [USSC EXCEPT !.msgs = Tail(USSC.msgs)]
        
USSCNext == 
    \/ USSCReceive

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:43:20 CET 2024 by jungc
\* Created Thu Feb 22 10:07:57 CET 2024 by jungc
