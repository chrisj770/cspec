-------------------------------- MODULE USC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, Common 

USCTypeOK == TRUE

USCInit == USCs = [u \in 1..NumUSCs |-> [
                    info |-> [address |-> "", 
                              reputation |-> 0,
                              userType |-> ""]]]
                    
USCNotRegistered(i) == USCs[i].info.address = ""                  
    
USCRegister(i, addr, type) == 
    /\ USCNotRegistered(i)
    /\ USCs' = [USCs EXCEPT ![i].info = [address |-> "something", 
                                         reputation |-> 1, 
                                         userType |-> type]]

=============================================================================
\* Modification History
\* Last modified Thu Feb 22 16:04:01 CET 2024 by jungc
\* Created Thu Feb 22 13:06:41 CET 2024 by jungc
