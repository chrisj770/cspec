------------------------------ MODULE Common ------------------------------
EXTENDS Sequences, Integers

CONSTANTS 
    NumWorkers,
    NumRequesters,
    NumUSCs
    
VARIABLES
    Workers,
    Requesters,
    USSC,
    USCs,
    TSSC,
    TSCs, 
    Time

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 12:29:56 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
