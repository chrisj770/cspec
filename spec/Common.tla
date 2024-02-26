------------------------------ MODULE Common ------------------------------
EXTENDS Sequences, Integers

CONSTANTS 
    NumWorkers,
    NumRequesters,
    NumUSCs,
    NULL
    
VARIABLES
    Workers,
    Requesters,
    USCs,
    TSCs, 
    Time, 
    NextPubkey, 
    Storage
    
IsWorker(address) == 
    \E i \in 1..NumWorkers : Workers[i].address = address
    
IsRequester(address) == 
    \E i \in 1..NumRequesters : Requesters[i].address = address
    
GetWorker(address) == 
    CHOOSE i \in 1..NumWorkers : Workers[i].address = address
    
GetRequester(address) == 
    CHOOSE i \in 1..NumRequesters : Requesters[i].address = address

SendMessage(recipient, message) == 
    IF recipient = "TSC"
         THEN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \union {message}]
    ELSE IF recipient = "USC"
         THEN USCs' = [USCs EXCEPT !.msgs = USCs.msgs \union {message}]
    ELSE IF IsRequester(recipient)
         THEN LET rid == GetRequester(recipient)
              IN Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
    ELSE IF IsWorker(recipient) 
         THEN LET wid == GetWorker(recipient)
              IN Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
    ELSE FALSE

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 11:07:02 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
