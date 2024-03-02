-------------------------- MODULE _Properties_TSC --------------------------
EXTENDS TSC

AllowedStateTransitions == {
    [start |-> "WORKING",
       end |-> {"CHECK_REPUTATION",
                "TERMINATED"}], 
                
    [start |-> "CHECK_REPUTATION", 
       end |-> {"WORKING", 
                "TERMINATED"}], 
    
    [start |-> "TERMINATED", 
       end |-> {}]
}

StateConsistency == 
    [](TSCs.state \in {s.start : s \in AllowedStateTransitions})
        
StateTransitions == 
    [][
        LET t == CHOOSE x \in AllowedStateTransitions : x.start = TSCs.state 
        IN TSCs'.state \in (t.end \union {t.start})
    ]_TSCs

TaskExpired(t) == 
    \/ /\ t.state \in {"Pending", "Available", "Unavailable"}
       /\ Time >= t.Sd
    \/ /\ t.state = "QEvaluating" 
       /\ Time >= t.Pd

TSCCancelsTasksWhenExpired == 
    [][
        IF \E t \in TSCs.tasks : TaskExpired(t)
        THEN LET taskId == CHOOSE t \in TSCs.tasks : TaskExpired(t)
                 updatedTask == CHOOSE t \in TSCs'.tasks : t.taskId = taskId
             IN updatedTask.state = "Canceled"
        ELSE TRUE
    ]_TSCs
    
TSCRemovesMessageAfterUpdate == 
    [][TSCs'.tasks # TSCs.tasks => \E m \in TSCs.msgs : m \notin TSCs'.msgs]_TSCs

Termination == 
    <>(TSCs.state = "TERMINATED")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ TSCCancelsTasksWhenExpired
    /\ TSCRemovesMessageAfterUpdate
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Sat Mar 02 14:42:11 CET 2024 by jungc
\* Created Sat Mar 02 14:14:04 CET 2024 by jungc
