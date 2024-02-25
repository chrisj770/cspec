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
    USSC,
    USCs,
    TSSC,
    TSCs, 
    Time, 
    NextPubkey, 
    Storage
    
IsWorker(pubkey) == 
    \E i \in 1..NumWorkers : Workers[i].pubkey = pubkey
    
IsRequester(pubkey) == 
    \E i \in 1..NumRequesters : Requesters[i].pubkey = pubkey

IsTSC(pubkey) == 
    \E tsc \in TSCs : tsc.pubkey = pubkey
    
GetWorker(pubkey) == 
    CHOOSE i \in 1..NumWorkers : Workers[i].pubkey = pubkey
    
GetRequester(pubkey) == 
    CHOOSE i \in 1..NumRequesters : Requesters[i].pubkey = pubkey
    
GetTSC(pubkey) == 
    CHOOSE tsc \in TSCs : tsc.pubkey = pubkey

SendMessage(pubkey, message) == 
    IF IsRequester(pubkey)
    THEN LET rid == GetRequester(pubkey)
         IN /\ Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
    ELSE IF IsWorker(pubkey) 
         THEN LET wid == GetWorker(pubkey)
              IN /\ Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
         ELSE LET tsc == GetTSC(pubkey) 
              IN /\ TSCs' = {IF t.pubkey = pubkey 
                             THEN [t EXCEPT !.msgs = t.msgs \union {message}]
                             ELSE t : t \in TSCs}

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 14:44:46 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
