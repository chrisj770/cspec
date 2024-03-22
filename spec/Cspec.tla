------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

(***************************************************************************)
(*                                  Cspec                                  *)
(*                                                                         *)
(* This file represents the entry-point to the TLA+ specification of       *)
(* C-SPEC, providing the high-level initialization states and behaviors    *)
(* for all entities within the system. It also defines events related to   *)
(* deadlines and message loss, which allows verification of the system     *) 
(* across a range of error scenarios.                                      *)
(***************************************************************************)

vars == <<Workers, Requesters, USCs, TSCs, NextUnique, Storage>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
TSC == INSTANCE TSC
USC == INSTANCE USC
Database == INSTANCE Database

RequesterProperties == INSTANCE _Properties_Requester
WorkerProperties == INSTANCE _Properties_Worker
TSCProperties == INSTANCE _Properties_TSC
USCProperties == INSTANCE _Properties_USC
DatabaseProperties == INSTANCE _Properties_Database

(***************************************************************************)
(*                              INITIALIZATION                             *)
(***************************************************************************)
Init == /\ Worker!Init
        /\ Requester!Init
        /\ TSC!Init
        /\ USC!Init
        /\ Database!Init
        /\ NextUnique = 1

(***************************************************************************)
(*                         INVARIANTS AND PROPERTIES                       *)
(***************************************************************************)
TypeOK == 
    /\ WorkerProperties!TypeOK
    /\ RequesterProperties!TypeOK
    /\ TSCProperties!TypeOK
    /\ USCProperties!TypeOK
    /\ DatabaseProperties!TypeOK
          
Properties == 
    /\ RequesterProperties!Properties
    /\ WorkerProperties!Properties
    /\ TSCProperties!Properties
    /\ USCProperties!Properties
    /\ DatabaseProperties!Properties
        
(***************************************************************************)
(*                         GLOBAL DEADLINE TRIGGERS                        *)
(***************************************************************************)

(***************************************************************************)
(* TriggerRegistrationDeadline: Represents elapsing of the USC's           *)
(* "RegistrationDeadline", after which new users cannot be registered.     *)
(* Allows Workers/Requesters to perform early termination behaviors.       *) 
(***************************************************************************)
TriggerRegistrationDeadline ==
    /\ ~USCs.RegistrationDeadline
    /\ USCs' = [USCs EXCEPT !.RegistrationDeadline = TRUE]
    /\ UNCHANGED <<Workers, Requesters, TSCs, Storage, NextUnique>>

(***************************************************************************)
(* TriggerRegistrationDeadline: Represents elapsing of the TSC's           *) 
(* "TaskPostDeadline", after which Requesters can no longer post tasks.    *)
(* Allows Workers/Requesters to terminate properly in early stages, rather *)
(* than wait indefinitely for successful task posting.                     *)
(***************************************************************************)    
TriggerTaskPostDeadline == 
    /\ USCs.RegistrationDeadline
    /\ ~TSCs.TaskPostDeadline
    /\ TSCs' = [TSCs EXCEPT !.TaskPostDeadline = TRUE]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>

(***************************************************************************)
(* TriggerRegistrationDeadline: Represents elapsing of any Worker's        *)
(* "TaskQueryDeadline", after which the Worker terminates if it has failed *)
(* to receive a list of active tasks from the TSC. Allows Workers to       *)
(* terminate properly in early stages, rather than wait indefinitely for   *) 
(* valid task lists.                                                       *)
(***************************************************************************)        
TriggerQueryTaskDeadline == 
    /\ USCs.RegistrationDeadline
    /\ TSCs.TaskPostDeadline
    /\ \A i \in 1..NumWorkers: ~Workers[i].TaskQueryDeadline
    /\ Workers' = [w \in 1..NumWorkers |-> [Workers[w] EXCEPT !.TaskQueryDeadline = TRUE]]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage, NextUnique>> 

(***************************************************************************)
(* TriggerNextTaskDeadline: Represents the elapsing of any task's          *)
(* Submission Deadline (Sd), Proving Deadline (Pd), or Task Deadline (Td)  *) 
(* (in the order specified) by updating all existing instances of the task *)
(* across Workers, Requesters, and the TSC.                                *)
(*                                                                         *)
(* These deadlines impose the following system requirements:               *)
(*                                                                         *) 
(*  (1) Prior to the Submission Deadline (Sd), the required number of task *) 
(*      participants must be registered with USC, and all Workers must     *)
(*      submit sensory data to Storage and hash to TSC.                    *) 
(*                                                                         *)
(*  (2) Prior to the Proving Deadline (Pd), the Requester and all Workers  *) 
(*      must submit evaluation results to TSC                              *)
(*                                                                         *)
(*  (3) Prior to the Task Deadline (Td), the user reputation update must   *)
(*      be complete.                                                       *)
(*                                                                         *)
(* If any requirement is not fulfilled upon reaching the respective        *)
(* deadline, it is the responsibility of each actor to take the            *)
(* appropriate action (e.g. continue to next task, mark task with state=   *)
(* "Canceled", etc.).                                                      *) 
(***************************************************************************)      
UpdateTask(task, taskId, Sd, Pd, Td) == 
    IF /\ task # NULL
       /\ task.taskId = taskId 
    THEN [task EXCEPT !.Sd = Sd, !.Pd = Pd, !.Td = Td]
    ELSE task 
    
UpdateMessages(messageSet, taskId, Sd, Pd, Td) == 
    {IF "tasks" \notin DOMAIN msg THEN msg
     ELSE [msg EXCEPT !.tasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in msg.tasks}]
    : msg \in messageSet}

TriggerNextTaskDeadline == 
    /\ USCs.RegistrationDeadline
    /\ TSCs.TaskPostDeadline
    /\ TSCs.tasks # {}
    /\ LET task == CHOOSE t \in TSCs.tasks : TRUE
           taskId == task.taskId
           Sd == TRUE
           Pd == task.Sd
           Td == task.Pd
       IN /\ TSCs' = [TSCs EXCEPT !.tasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in TSCs.tasks}]
          /\ Requesters' = [i \in 1..NumRequesters |-> [Requesters[i] EXCEPT
                !.tasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Requesters[i].tasks},
                !.currentTask = UpdateTask(Requesters[i].currentTask, taskId, Sd, Pd, Td),
                !.msgs = UpdateMessages(Requesters[i].msgs, taskId, Sd, Pd, Td)]]
          /\ Workers' = [i \in 1..NumWorkers |-> [Workers[i] EXCEPT
                !.pendingTasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Workers[i].pendingTasks},
                !.unconfirmedTasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Workers[i].unconfirmedTasks},
                !.confirmedTasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Workers[i].confirmedTasks},
                !.currentTask = UpdateTask(Workers[i].currentTask, taskId, Sd, Pd, Td),
                !.msgs = UpdateMessages(Workers[i].msgs, taskId, Sd, Pd, Td)]]
    /\ UNCHANGED <<USCs, Storage, NextUnique>>
    
(***************************************************************************)
(*                          SIMULATED MESSAGE LOSS                         *)
(***************************************************************************)

(***************************************************************************)
(* WorkerMessageLoss: Represents the scenario in which a message sent to   *)
(* any Worker fails to be received due to lossy communication channels.    *)    
(***************************************************************************)
WorkerMessageLoss == 
    /\ \E i \in 1..NumWorkers : Cardinality(Workers[i].msgs) > 0
    /\ LET i == CHOOSE j \in 1..NumWorkers : Cardinality(Workers[j].msgs) > 0
           msg == CHOOSE m \in Workers[i].msgs : TRUE
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg}]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage, NextUnique>>

(***************************************************************************)
(* RequesterMessageLoss: Represents the scenario in which a message sent   *)
(* to any Requester fails to be received due to lossy communication        *)
(* channels.                                                               *)    
(***************************************************************************)    
RequesterMessageLoss == 
    /\ \E i \in 1..NumRequesters : Cardinality(Requesters[i].msgs) > 0
    /\ LET i == CHOOSE j \in 1..NumRequesters : Cardinality(Requesters[j].msgs) > 0
           msg == CHOOSE m \in Requesters[i].msgs : TRUE
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg}]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage, NextUnique>>

(***************************************************************************)
(* TSCMessageLoss: Represents the scenario in which a message sent to the  *)
(* TSC fails to be received due to lossy communication channels.           *)    
(***************************************************************************)    
TSCMessageLoss == 
    /\ Cardinality(TSCs.msgs) > 0
    /\ LET msg == CHOOSE m \in TSCs.msgs : TRUE
       IN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>

(***************************************************************************)
(* USCMessageLoss: Represents the scenario in which a message sent to the  *)
(* USC fails to be received due to lossy communication channels.           *)    
(***************************************************************************)   
USCMessageLoss == 
    /\ Cardinality(USCs.msgs) > 0
    /\ LET msg == CHOOSE m \in USCs.msgs : TRUE
       IN USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, TSCs, Storage, NextUnique>>

(***************************************************************************)
(* StorageMessageLoss: Represents the scenario in which a message sent to  *)
(* Storage fails to be received due to lossy communication channels.       *)    
(***************************************************************************)     
StorageMessageLoss ==
    /\ Cardinality(Storage.msgs) > 0
    /\ LET msg == CHOOSE m \in Storage.msgs : TRUE
       IN Storage' = [Storage EXCEPT !.msgs = Storage.msgs \ {msg}] 
    /\ UNCHANGED <<Workers, Requesters, TSCs, USCs, NextUnique>>
    
MessageLoss == 
    \/ WorkerMessageLoss
    \/ RequesterMessageLoss
    \/ TSCMessageLoss
    \/ USCMessageLoss
    \/ StorageMessageLoss

(***************************************************************************)
(*                        ACTION AND SPEC DEFINITIONS                      *)
(***************************************************************************)        
Next == \/ /\ \/ Worker!Next
              \/ Requester!Next
           /\ UNCHANGED <<NextUnique>>
        \/ /\ \/ TSC!Next
              \/ USC!Next
           /\ UNCHANGED <<Storage>>
        \/ /\ Database!Next
           /\ UNCHANGED <<TSCs, USCs>>
        \/ TriggerRegistrationDeadline
        \/ TriggerTaskPostDeadline
        \/ TriggerQueryTaskDeadline
        \/ TriggerNextTaskDeadline
        \/ MessageLoss

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Fri Mar 22 10:45:20 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
