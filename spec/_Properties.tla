---------------------------- MODULE _Properties ----------------------------

MessageAdded(before, after)== 
    \E m \in after : m \notin before
    
MessageRemoved(before, after) == 
    \E m \in before : m \notin after

=============================================================================
\* Modification History
\* Last modified Mon Mar 04 09:21:57 CET 2024 by jungc
\* Created Sat Mar 02 14:49:49 CET 2024 by jungc
