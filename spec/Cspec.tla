------------------------------- MODULE Cspec -------------------------------
EXTENDS FiniteSets, Common

CONSTANT Tasks

vars == <<Workers, Requesters, USCs, TSCs, NextUnique, Storage>>

Requester == INSTANCE Requester
Worker == INSTANCE Worker
Blockchain == INSTANCE Blockchain
Database == INSTANCE Database

RequesterProperties == INSTANCE _Properties_Requester
WorkerProperties == INSTANCE _Properties_Worker
TSCProperties == INSTANCE _Properties_TSC

TypeOK == /\ WorkerProperties!TypeOK
          /\ RequesterProperties!TypeOK
          /\ Blockchain!TypeOK
          /\ Database!TypeOK
    
Init == /\ Worker!Init
        /\ Requester!Init
        /\ Blockchain!Init
        /\ Database!Init
        /\ NextUnique = 1
        
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
                !.unconfirmedTasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Workers[i].unconfirmedTasks},
                !.confirmedTasks = {UpdateTask(t, taskId, Sd, Pd, Td) : t \in Workers[i].confirmedTasks},
                !.currentTask = UpdateTask(Workers[i].currentTask, taskId, Sd, Pd, Td),
                !.msgs = UpdateMessages(Workers[i].msgs, taskId, Sd, Pd, Td)]]
    /\ UNCHANGED <<USCs, Storage, NextUnique>>
    
Terminated == 
    /\ \A i \in 1..NumWorkers : Workers[i].state = "TERMINATED"
    /\ \A j \in 1..NumRequesters : Requesters[j].state = "TERMINATED"
    /\ TSCs.state = "TERMINATED" 
    /\ USCs.state = "TERMINATED"
    /\ Storage.state = "TERMINATED"
        
Next == \/ /\ \/ Worker!Next
              \/ Requester!Next
           /\ UNCHANGED <<NextUnique>>
        \/ /\ Blockchain!Next
           /\ UNCHANGED <<Storage>>
        \/ /\ Database!Next
           /\ UNCHANGED <<TSCs, USCs>>
        \/ TriggerRegistrationDeadline
        \/ TriggerTaskPostDeadline
        \/ TriggerQueryTaskDeadline
        \*\/ TriggerNextTaskDeadline

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Properties == 
    /\ RequesterProperties!Properties
    /\ WorkerProperties!Properties
    /\ TSCProperties!Properties

=============================================================================
\* Modification History
\* Last modified Sun Mar 03 16:37:25 CET 2024 by jungc
\* Created Thu Feb 22 09:05:22 CET 2024 by jungc
