-------------------------------- MODULE USSC --------------------------------
EXTENDS Sequences, USC, TLC, Common

CONSTANT RegistrationDeadline

USSCTypeOK == TRUE 

USSCInit == 
    /\ USSC = [msgs |-> {}]
    /\ NextPubkey = 1

USSCReceiveRegister(msg) == \E usc \in 1..NumUSCs :
    /\ USCNotRegistered(usc)
    /\ NextPubkey' = NextPubkey + 1
    /\ LET newKey == ToString(NextPubkey) IN
       /\ USCRegister(usc, newKey, msg.userType)
       /\ IF msg.userType = "WORKER" 
          THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \union 
                             {[type |-> "REGISTERED", 
                               src |-> "USSC",  
                               pubkey |-> newKey]}]
               /\ UNCHANGED <<Requesters, TSSC, TSCs>>
          ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \union
                                {[type |-> "REGISTERED", 
                                  src |-> "USSC",  
                                  pubkey |-> newKey]}]
               /\ UNCHANGED <<Workers, TSSC, TSCs>>
            
USSCCheckUser(pubkey, userType) == 
    \E usc \in 1..NumUSCs : USCIsRegistered(usc, pubkey, userType)
    
USSCGetUser(pubkey, userType) == 
    LET i == CHOOSE j \in 1..NumUSCs :
                /\ USCs[j].info.pubkey = pubkey
                /\ USCs[j].info.userType = userType 
    IN USCs[i]
    
USSCReceive == 
    /\ \E msg \in USSC.msgs : msg.type = "REGISTER"
    /\ LET msg == CHOOSE m \in USSC.msgs : m.type = "REGISTER" IN
       /\ USSCReceiveRegister(msg)
       /\ USSC' = [USSC EXCEPT !.msgs = USSC.msgs \ {msg}]
        
USSCNext == 
    USSCReceive

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 12:59:24 CET 2024 by jungc
\* Created Thu Feb 22 10:07:57 CET 2024 by jungc
