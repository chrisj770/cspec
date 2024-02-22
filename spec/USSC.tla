-------------------------------- MODULE USSC --------------------------------
EXTENDS Sequences, USC, Common

USSCTypeOK == TRUE 

USSCInit == USSC = [msgs |-> <<>>]

USSCReceiveRegister(msg) == \E usc \in 1..NumUSCs :
    /\ USCRegister(usc, msg.src, msg.userType)
    /\ IF msg.userType = "WORKER" 
       THEN /\ Workers' = [Workers EXCEPT ![msg.src].msgs = Workers[msg.src].msgs \o 
                            <<[type |-> "REGISTERED", src |-> "USSC",  pubkey |-> USCs[usc].info.address]>>]
            /\ UNCHANGED <<Requesters, TSSC, TSCs>>
       ELSE /\ Requesters' = [Requesters EXCEPT ![msg.src].msgs = Requesters[msg.src].msgs \o 
                                <<[type |-> "REGISTERED", src |-> "USSC",  pubkey |-> USCs[usc].info.address]>>]
            /\ UNCHANGED <<Workers, TSSC, TSCs>>

\* USSCReceiveGetUser(message) == TRUE

\* USSCReceiveUpdate(message) == TRUE

\* USSCReceiveInvalid(message) == TRUE
    
USSCReceive == 
    /\ Len(USSC.msgs) > 0
    /\ LET message == Head(USSC.msgs) IN
          USSCReceiveRegister(message)
          \* IF message.type = "REGISTER" THEN USSCReceiveRegister(message)
          \* ELSE IF message.type = "GET_USER" THEN USSCReceiveGetUser(message)
          \* ELSE IF message.type = "UPDATE" THEN USSCReceiveUpdate(message)
          \* ELSE USSCReceiveInvalid(message)
    /\ USSC' = [USSC EXCEPT !.msgs = Tail(USSC.msgs)]
        
USSCNext == 
    \/ USSCReceive

=============================================================================
\* Modification History
\* Last modified Thu Feb 22 16:17:15 CET 2024 by jungc
\* Created Thu Feb 22 10:07:57 CET 2024 by jungc
