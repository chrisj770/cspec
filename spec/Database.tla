------------------------------ MODULE Database ------------------------------
EXTENDS Common 

TypeOK == TRUE

Init == Storage = [msgs |-> {}, 
                   data |-> {}]

ReceiveSubmitData == 
    /\ \E msg \in Storage.msgs : /\ msg.type = "SUBMIT_DATA"
                                 /\ \E i \in 1..NumWorkers : Workers[i].pubkey = msg.pubkey
    /\ LET msg == CHOOSE m \in Storage.msgs : m.type = "SUBMIT_DATA"
           data == msg.data
           hash == "Somehash" IN 
        /\ Storage' = [Storage EXCEPT !.data = Storage.data \union {<<hash, data>>},
                                      !.msgs = Storage.msgs \ {msg}]
        /\ LET wid == CHOOSE i \in 1..NumWorkers : Workers[i].pubkey = msg.pubkey IN 
            /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {[type |-> "HASH", 
                                                                                  src |-> "STORAGE", 
                                                                                  hash |-> hash]}]
    /\ UNCHANGED <<Requesters>>

Next == 
    /\ ReceiveSubmitData

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 11:07:16 CET 2024 by jungc
\* Created Sun Feb 25 10:53:35 CET 2024 by jungc
