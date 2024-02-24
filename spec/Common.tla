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
    NextPubkey

=============================================================================
\* Modification History
\* Last modified Sat Feb 24 10:43:24 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
