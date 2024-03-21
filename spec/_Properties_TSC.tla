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
(* LIVENESS: If TSC receives a CONFIRM_TASK message from a Worker for any  *) 
(* "Available" task for which they are qualified (via checkQ) and space is *)
(* available, then the Worker must be added as a participant.              *)
(* Alternatively, if the Worker is unqualified, space is not available, or *)
(* the task is not in state="Available", then the Worker must NOT be added *)
(* as a participant.                                                       *)
(***************************************************************************)
TSCAcceptsQualifiedWorkers == 
    [][
        IF /\ \E m \in TSCs.msgs : m.type = "CONFIRM_TASK" 
           /\ LET msg == CHOOSE m \in TSCs.msgs : m.type = "CONFIRM_TASK"
              IN \E t \in TSCs.tasks : msg.task = t.address
           /\ TSCs.TaskPostDeadline
           /\ ~TaskPostDeadlineUpdated
           /\ ~TaskDeadlineUpdated
           /\ ~TaskStateUpdated
           /\ ~MessageAdded(TSCs.msgs, TSCs'.msgs)
           /\ ~MessageLost
        THEN LET msg == CHOOSE m \in TSCs.msgs : m.type = "CONFIRM_TASK"
                 worker == CHOOSE w \in USCs.users : msg.from = w.pk
                 task == CHOOSE t \in TSCs.tasks : msg.task = t.address
                 newTask == CHOOSE t \in TSCs'.tasks : msg.task = t.address
             IN IF /\ task.state = "Available"
                   /\ task.checkQ[worker.reputation]
                   /\ Cardinality(task.participants) < task.numParticipants
                THEN msg.from \in newTask.participants                 
                ELSE msg.from \notin newTask.participants
        ELSE TRUE
    ]_TSCs
    
(***************************************************************************)
(* LIVENESS: If TSC receives a SUBMIT_HASH message from a Worker, the hash *) 
(* contained in the message must already exist as a data entry within      *)
(* decentralized Storage.                                                  *)
(***************************************************************************)
TSCAllSubmittedHashesExist ==
    [](
        IF \E m \in TSCs.msgs : m.type = "SUBMIT_HASH" 
        THEN LET msg == CHOOSE m \in TSCs.msgs : m.type = "SUBMIT_HASH"
             IN \E data \in Storage.data :
                /\ data.address = msg.from
                /\ data.hash = msg.hash
        ELSE TRUE 
    )   

(***************************************************************************)
(* LIVENESS: If any task is updated with state="Unavailable", then the     *)
(* required number of participants must have been successfully registered. *)
(***************************************************************************)
TSCUnavailableTaskConditions == 
    [][
        IF \E t1 \in TSCs.tasks : \A t2 \in TSCs'.tasks : 
           t1.taskId = t2.taskId => /\ t1.state = "Available"  
                                    /\ t2.state = "Unavailable"
        THEN LET newTask == CHOOSE t2 \in TSCs'.tasks : \A t1 \in TSCs.tasks:
                            t1.taskId = t2.taskId => /\ t1.state = "Available"
                                                     /\ t2.state = "Unavailable"
             IN Cardinality(newTask.participants) = newTask.numParticipants
        ELSE TRUE
    ]_TSCs

(***************************************************************************)
(* LIVENESS: If any task is updated with state="QEvaluating", then the     *)
(* following conditions must be fulfilled:                                 *)
(*                                                                         *)
(*  (1) The required number of participants hav  been registered.          *) 
(*  (2) The required number of hashes have been submitted (equal to the    *) 
(*       number of participants).                                          *)
(*                                                                         *)
(***************************************************************************)
TSCQEvaluatingTaskConditions == 
    [][
        IF \E t1 \in TSCs.tasks : \A t2 \in TSCs'.tasks : 
           t1.taskId = t2.taskId => /\ t1.state = "Unavailable"  
                                    /\ t2.state = "QEvaluating"
        THEN LET newTask == CHOOSE t2 \in TSCs'.tasks : \A t1 \in TSCs.tasks:
                            t1.taskId = t2.taskId => /\ t1.state = "Unavailable"
                                                     /\ t2.state = "QEvaluating"
             IN /\ Cardinality(newTask.participants) = newTask.numParticipants
                /\ Cardinality(newTask.hashes) = newTask.numParticipants
        ELSE TRUE
    ]_TSCs

(***************************************************************************)
(* LIVENESS: If any task is updated with state="Completed", the following  *)
(* conditions must be fulfilled:                                           *)
(*                                                                         *)
(*  (1) All requirements from "TSCQEvaluatingTaskConditions" must also     *)
(*        have been fulfilled.                                             *)
(*  (3) The Requester has submitted evaluation results.                    *)
(*  (4) All participants have submitted evaluation results.                *)
(*                                                                         *)
(***************************************************************************)
TSCCompletedTaskConditions == 
    [][
        IF \E t1 \in TSCs.tasks : \A t2 \in TSCs'.tasks : 
           t1.taskId = t2.taskId => /\ t1.state = "QEvaluating"  
                                    /\ t2.state = "Completed"
        THEN LET newTask == CHOOSE t2 \in TSCs'.tasks : \A t1 \in TSCs.tasks:
                            t1.taskId = t2.taskId => /\ t1.state = "QEvaluating"
                                                     /\ t2.state = "Completed"
             IN /\ Cardinality(newTask.participants) = newTask.numParticipants
                /\ Cardinality(newTask.hashes) = newTask.numParticipants
                /\ Cardinality(newTask.requesterWeights) = 1
                /\ Cardinality(newTask.workerWeights) = newTask.numParticipants
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
    /\ TSCAcceptsQualifiedWorkers
    /\ TSCAllSubmittedHashesExist
    /\ TSCUnavailableTaskConditions
    /\ TSCQEvaluatingTaskConditions
    /\ TSCCompletedTaskConditions
    /\ TSCCancelsTasksWhenExpired
    /\ TSCAllTasksFinishedOnTermination
    /\ Termination

=============================================================================
\* Modification History
\* Last modified Thu Mar 21 09:59:45 CET 2024 by jungc
\* Created Sat Mar 02 14:14:04 CET 2024 by jungc
