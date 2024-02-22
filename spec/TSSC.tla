-------------------------------- MODULE TSSC --------------------------------
EXTENDS Sequences, TSC, Common

TSSCTypeOK == TRUE

TSSCInit == TSSC = [msgs |-> <<>>]
        
TSSCReceivePost(message) == TRUE
TSSCReceiveQuery(message) == TRUE
TSSCReceiveInvalid(message) == TRUE
    
TSSCRecieve == 
    /\ LET message == Head(TSSC.msgs) IN
        IF message.type = "POST_TASK" THEN TSSCReceivePost(message)
        ELSE IF message.type = "QUERY_TASK" THEN TSSCReceiveQuery(message)
        ELSE TSSCReceiveInvalid(message)

=============================================================================
\* Modification History
\* Last modified Thu Feb 22 16:17:08 CET 2024 by jungc
\* Created Thu Feb 22 09:13:46 CET 2024 by jungc
