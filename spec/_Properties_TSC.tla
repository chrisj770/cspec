-------------------------- MODULE _Properties_TSC --------------------------
EXTENDS TSC, _Properties

(***************************************************************************)
(*                             STATE CONSISTENCY                           *)
(***************************************************************************)
AllowedStateTransitions == {
    [start |-> "WORKING",
       end |-> {}]
}

StateConsistency == 
    [][TSCs.state \in {s.start : s \in AllowedStateTransitions}]_TSCs
        
StateTransitions == 
    [][
        LET t == CHOOSE x \in AllowedStateTransitions : x.start = TSCs.state 
        IN TSCs'.state \in (t.end \union {t.start})
    ]_TSCs
    
(***************************************************************************)
(*                             TYPE CONSISTENCY                            *)
(***************************************************************************)
TypeOK == 
    /\ TSCs.state \in {s.start : s \in AllowedStateTransitions}
    /\ \A msg \in TSCs.msgs : MessageOK(msg)
    /\ KeyOK(TSCs.pk)
    /\ \A t \in TSCs.tasks : TaskOK(t)
    /\ TSCs.TaskPostDeadline \in {TRUE, FALSE}
    
(***************************************************************************)
(*                                PROPERTIES                               *)
(***************************************************************************)
TaskDeadlineUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        \/ t1.Sd # t2.Sd
        \/ t1.Pd # t2.Pd
        \/ t1.Td # t2.Td 
        
TaskStateUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        t1.state # t2.state 
    
TSCAllTasksComplete == 
    <>[](\A t \in TSCs.tasks : t.state \in {"Canceled", "Completed"})

TSCCancelsTasksWhenExpired == 
    [][
        IF /\ \E t \in TSCs.tasks : TaskExpired(t)
           /\ ~TaskDeadlineUpdated
           /\ ~MessageAdded(TSCs.msgs, TSCs'.msgs)
        THEN LET task == CHOOSE t \in TSCs.tasks : TaskExpired(t)
                 updatedTask == CHOOSE t \in TSCs'.tasks : t.taskId = task.taskId
             IN updatedTask.state = "Canceled"
        ELSE TRUE
    ]_TSCs
    
TSCRemovesMessageAfterUpdate == 
    [][
       IF /\ TSCs'.tasks # TSCs.tasks 
          /\ ~TaskDeadlineUpdated 
          /\ ~TaskStateUpdated
       THEN MessageRemoved(TSCs.msgs, TSCs'.msgs)
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
\* Last modified Wed Mar 13 10:06:41 CET 2024 by jungc
\* Created Sat Mar 02 14:14:04 CET 2024 by jungc
