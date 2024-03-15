------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

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
TriggerRegistrationDeadline ==
    /\ ~USCs.RegistrationDeadline
    /\ USCs' = [USCs EXCEPT !.RegistrationDeadline = TRUE]
    /\ UNCHANGED <<Workers, Requesters, TSCs, Storage, NextUnique>>
    
TriggerTaskPostDeadline == 
    /\ USCs.RegistrationDeadline
    /\ ~TSCs.TaskPostDeadline
    /\ TSCs' = [TSCs EXCEPT !.TaskPostDeadline = TRUE]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>
    
TriggerQueryTaskDeadline == 
    /\ USCs.RegistrationDeadline
    /\ TSCs.TaskPostDeadline
    /\ \A i \in 1..NumWorkers: ~Workers[i].TaskQueryDeadline
    /\ Workers' = [w \in 1..NumWorkers |-> [Workers[w] EXCEPT !.TaskQueryDeadline = TRUE]]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage, NextUnique>> 
    
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
WorkerMessageLoss == 
    /\ \E i \in 1..NumWorkers : Cardinality(Workers[i].msgs) > 0
    /\ LET i == CHOOSE j \in 1..NumWorkers : Cardinality(Workers[j].msgs) > 0
           msg == CHOOSE m \in Workers[i].msgs : TRUE
       IN Workers' = [Workers EXCEPT ![i].msgs = Workers[i].msgs \ {msg}]
    /\ UNCHANGED <<Requesters, TSCs, USCs, Storage, NextUnique>>
    
RequesterMessageLoss == 
    /\ \E i \in 1..NumRequesters : Cardinality(Requesters[i].msgs) > 0
    /\ LET i == CHOOSE j \in 1..NumRequesters : Cardinality(Requesters[j].msgs) > 0
           msg == CHOOSE m \in Requesters[i].msgs : TRUE
       IN Requesters' = [Requesters EXCEPT ![i].msgs = Requesters[i].msgs \ {msg}]
    /\ UNCHANGED <<Workers, TSCs, USCs, Storage, NextUnique>>
    
TSCMessageLoss == 
    /\ Cardinality(TSCs.msgs) > 0
    /\ LET msg == CHOOSE m \in TSCs.msgs : TRUE
       IN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, USCs, Storage, NextUnique>>

USCMessageLoss == 
    /\ Cardinality(USCs.msgs) > 0
    /\ LET msg == CHOOSE m \in USCs.msgs : TRUE
       IN USCs' = [USCs EXCEPT !.msgs = USCs.msgs \ {msg}]
    /\ UNCHANGED <<Workers, Requesters, TSCs, Storage, NextUnique>>
    
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
(*                   STATE TRANSITION AND SPEC DEFINITIONS                 *)
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
\* Last modified Fri Mar 15 12:58:42 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
