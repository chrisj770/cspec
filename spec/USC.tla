-------------------------------- MODULE USC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, Common 

USCTypeOK == TRUE

USCInit == USCs = [u \in 1..NumUSCs |-> [
                    info |-> [pubkey |-> "",
                              reputation |-> 0,
                              userType |-> ""]]]
                    
USCNotRegistered(i) == USCs[i].info.pubkey = ""

USCIsRegistered(i, key, type) == 
    /\ USCs[i].info.pubkey = key
    /\ USCs[i].info.userType = type  
    
USCRegister(i, key, type) == 
    /\ USCNotRegistered(i)
    /\ USCs' = [USCs EXCEPT ![i].info = [pubkey |-> key,
                                         reputation |-> 1, 
                                         userType |-> type]]

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 10:02:28 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
