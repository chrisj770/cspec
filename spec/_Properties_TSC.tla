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
    [][TSCs.state \in {s.start : s \in AllowedStateTransitions}]_TSCs
        
StateTransitions == 
    [][
        LET t == CHOOSE x \in AllowedStateTransitions : x.start = TSCs.state 
        IN TSCs'.state \in (t.end \union {t.start})
    ]_TSCs
           
TaskDeadlinesUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        \/ t1.Sd # t2.Sd
        \/ t1.Pd # t2.Pd
        \/ t1.Td # t2.Td 
        
TaskStateUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        t1.state # t2.state 
        
MessageAdded == 
    \E m \in TSCs'.msgs : m \notin TSCs.msgs
    
MessageRemoved == 
    \E m \in TSCs.msgs : m \notin TSCs'.msgs
    

TSCAllTasksComplete == 
    <>[](\A t \in TSCs.tasks : t.state \in {"Canceled", "Completed"})

TSCCancelsTasksWhenExpired == 
    [][
        IF /\ \E t \in TSCs.tasks : TaskExpired(t)
           /\ ~TaskDeadlinesUpdated
           /\ ~MessageAdded
        THEN LET task == CHOOSE t \in TSCs.tasks : TaskExpired(t)
                 updatedTask == CHOOSE t \in TSCs'.tasks : t.taskId = task.taskId
             IN updatedTask.state = "Canceled"
        ELSE TRUE
    ]_TSCs
    
TSCRemovesMessageAfterUpdate == 
    [][
       IF /\ TSCs'.tasks # TSCs.tasks 
          /\ ~TaskDeadlinesUpdated 
          /\ ~TaskStateUpdated
       THEN MessageRemoved
       ELSE TRUE
    ]_TSCs


Termination == 
    <>[](TSCs.state = "WORKING")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ TSCAllTasksComplete
    /\ TSCCancelsTasksWhenExpired
    /\ TSCRemovesMessageAfterUpdate
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Sun Mar 03 21:00:14 CET 2024 by jungc
\* Created Sat Mar 02 14:14:04 CET 2024 by jungc
