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
TaskPostDeadlineUpdated == 
    ~TSCs.TaskPostDeadline /\ TSCs'.TaskPostDeadline

TaskDeadlineUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        \/ t1.Sd # t2.Sd
        \/ t1.Pd # t2.Pd
        \/ t1.Td # t2.Td 
        
TaskStateUpdated == 
    \E t1 \in TSCs'.tasks : \A t2 \in TSCs.tasks: t1.taskId = t2.taskId =>
        t1.state # t2.state 
        
MessageLost ==
    /\ \E m \in TSCs.msgs : m \notin TSCs'.msgs
    /\ LET removed == CHOOSE m \in TSCs.msgs : m \notin TSCs'.msgs
       IN TSCs' = [TSCs EXCEPT !.msgs = TSCs'.msgs \ {removed}]

(***************************************************************************)
(* LIVENESS: If TSC receives a POST_TASKS message from a Requester before  *)
(* the TaskPostDeadline, the number of active tasks should increase by the *)
(* quantity of tasks specified in the message.                             *)
(***************************************************************************)
TSCAddsTasksWhenReceived == 
    [][
        IF /\ \E m \in TSCs.msgs : m.type = "POST_TASKS"
           /\ ~TSCs.TaskPostDeadline
           /\ ~TaskPostDeadlineUpdated
           /\ ~TaskDeadlineUpdated
           /\ ~MessageAdded(TSCs.msgs, TSCs'.msgs)
           /\ ~MessageLost
        THEN LET msg == CHOOSE m \in TSCs.msgs : m.type = "POST_TASKS"
             IN Cardinality(TSCs'.tasks) = Cardinality(TSCs.tasks) + Len(msg.tasks)
        ELSE TRUE
    ]_TSCs

(***************************************************************************)
(* LIVENESS: When a task deadline elapses without the task reaching one of *)
(* the required states, TSC must immediately update the task with state    *)
(* "Canceled" to prevent any further processing.                           *)
(***************************************************************************)    
TSCCancelsTasksWhenExpired == 
    [][
        IF /\ \E t \in TSCs.tasks : TaskExpired(t)
           /\ ~TaskPostDeadlineUpdated
           /\ ~TaskDeadlineUpdated
           /\ ~MessageAdded(TSCs.msgs, TSCs'.msgs)
           /\ ~MessageLost
        THEN LET task == CHOOSE t \in TSCs.tasks : TaskExpired(t)
                 updatedTask == CHOOSE t \in TSCs'.tasks : t.taskId = task.taskId
             IN updatedTask.state = "Canceled"
        ELSE TRUE
    ]_TSCs
    
(***************************************************************************)
(* TERMINATION: All tasks added by Requesters must reach state "Canceled"  *)
(* or "Completed" by conclusion of the process.                            *)
(***************************************************************************)    
TSCAllTasksFinishedOnTermination == 
    <>[](\A t \in TSCs.tasks : t.state \in {"Canceled", "Completed"})

(***************************************************************************)
(* TERMINATION: TSC remains in "WORKING" state indefinitely by conclusion  *)
(* of the process.                                                         *)
(***************************************************************************)
Termination == 
    <>[](TSCs.state = "WORKING")

Properties == 
    /\ StateConsistency
    /\ StateTransitions
    /\ TSCAddsTasksWhenReceived
    /\ TSCCancelsTasksWhenExpired
    /\ TSCAllTasksFinishedOnTermination
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Fri Mar 15 13:50:13 CET 2024 by jungc
\* Created Sat Mar 02 14:14:04 CET 2024 by jungc
