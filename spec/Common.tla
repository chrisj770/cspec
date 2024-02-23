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
    TSCs

=============================================================================
\* Modification History
\* Last modified Fri Feb 23 08:15:57 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
