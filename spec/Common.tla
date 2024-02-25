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

=============================================================================
\* Modification History
\* Last modified Sun Feb 25 10:52:21 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
