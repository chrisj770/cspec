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
    NextUserId

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 16:06:08 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
