------------------------------ MODULE Common ------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS 
    NumWorkers,
    NumRequesters, 
    Tasks,
    NULL
    
VARIABLES
    Workers,
    Requesters,
    USCs,
    TSCs, 
    NextUnique, 
    Storage

(***************************************************************************)
(*              GLOBALLY-AVAILABLE CHECKS FOR TYPE CONSISTENCY             *)
(***************************************************************************)
KeyOK(k) == 
    /\ \A f \in {"address", "type"} : f \in DOMAIN k
    /\ \/ k.address \in {ToString(t) : t \in 0..NextUnique}
       \/ k.address \in {"TSC", "USC", "STORAGE"}
    /\ k.type \in {"public_key", "private_key"}
        
KeyshareOK(k) == 
    /\ KeyOK(k)
    /\ "share" \in DOMAIN k
    /\ k.share \in 0..NextUnique
    
WeightsOK(w) == 
    TRUE
   
WorkerTaskOK(t) == 
    /\ \A f \in {"taskId", "address", "category", "state", "owner", 
                 "numParticipants", "Sd", "Pd", "Td"} :
          f \in DOMAIN t
    /\ t.taskId \in 1..Len(Tasks)
    /\ t.address \in {ToString(a) : a \in 0..NextUnique}
    /\ t.category \in {"PlaceholderCategory"}
    /\ t.state \in {"Pending", "Available", "Unavailable", 
                    "QEvaluating", "Completed", "Canceled"}
    /\ KeyOK(t.owner)
    /\ t.numParticipants \in Int
    /\ t.Sd \in {TRUE, FALSE}
    /\ t.Pd \in {TRUE, FALSE}
    /\ t.Td \in {TRUE, FALSE}
       
TaskOK(t) == 
    /\ WorkerTaskOK(t)
    /\ \A f \in {"participants", "globalReputationThreshold", 
                 "expertiseReputationThreshold", "checkQ", "QEvaluate", 
                 "hashes", "requesterWeights", "workerWeights"} :
          f \in DOMAIN t
    /\ \A p \in t.participants : KeyOK(p)
    /\ t.globalReputationThreshold \in Int
    /\ t.expertiseReputationThreshold \in Int
    /\ \A h \in t.hashes : h \in {ToString(a) : a \in 0..NextUnique}
    /\ \/ t.requesterWeights = NULL 
       \/ WeightsOK(t.requesterWeights)
    /\ \A w \in t.workerWeights : WeightsOK(w)
    
MessageOK(msg) == 
    /\ \A f \in {"from", "type"} : f \in DOMAIN msg
    /\ KeyOK(msg.from)

(***************************************************************************)
(*                  INTER-PROCESS COMMUNICATION METHODS                    *)
(***************************************************************************)
GetWorker(public_key) == 
    CHOOSE i \in 1..NumWorkers : Workers[i].pk = public_key
    
GetRequester(public_key) == 
    CHOOSE i \in 1..NumRequesters : Requesters[i].pk = public_key
    
SendTSCMessage(message) == 
    TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \union {message}]

SendUSCMessage(message) == 
    USCs' = [USCs EXCEPT !.msgs = USCs.msgs \union {message}]
    
SendStorageMessage(message) == 
    Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {message}]
    
SendRequesterMessage(recipient, message) == 
    /\ \E i \in 1..NumRequesters : Requesters[i].pk = recipient
    /\ LET rid == GetRequester(recipient)
       IN Requesters' = [Requesters EXCEPT ![rid].msgs = 
                            Requesters[rid].msgs \union {message}]
                            
SendWorkerMessage(recipient, message) == 
    /\ \E i \in 1..NumWorkers : Workers[i].pk = recipient
    /\ LET wid == GetWorker(recipient)
       IN Workers' = [Workers EXCEPT ![wid].msgs =
                             Workers[wid].msgs \union {message}]
  
(* 
\* (TODO: Might need this for later) 
SendWorkerBroadcast(recipientSet, message) == 
    Workers' = [i \in 1..NumWorkers |-> [Workers[i] EXCEPT
                 !.msgs = IF Workers[i].pk \in recipientSet
                          THEN Workers[i].msgs \union {message}
                          ELSE Workers[i].msgs]]
*)

(***************************************************************************)
(*                        ENCRYPTION / DECRYPTION                          *)
(***************************************************************************)

(***************************************************************************)
(* During registration, each user receive a pair of public/private         *)
(* encryption keys, which are used to encrypt/decrypt all instances of     *)
(* sensory data that gets exchanged with Database. These keys are          *)
(* represented as structs of the following format:                         *)
(*                                                                         *)
(* Key == [address |-> (encryptor_address),                                *)
(*            type |-> ("public_key" or "private_key")                     *)
(*           share |-> (Int)]                           <----OPTIONAL      *)
(*                                                                         *)
(* We also store each instance of encrypted data with the key used for     *)
(* encryption, as formatted below:                                         *)
(*                                                                         *)
(* EncryptedData == [encryptedData |-> (data),                             *)
(*                   encryptionKey |-> (key)]                              *)
(*                                                                         *)
(* Any user "N" can encrypt data using their public key "Npk", or some     *)
(* share of the public key "Npk_1", "Npk_2", ..., "Npk_n". Once this       *)
(* occurs, the data can only be accessed by decrypting it via the          *)
(* corresponding private key "Nsk", or some share of the private key       *)
(* "Nsk_1", "Nsk_2", ..., "Nsk_n". These operations are represented via    *)
(* the methods below.                                                      *)
(***************************************************************************)
Encrypt(data, encryptionKey) == 
    [encryptedData |-> data, encryptionKey |-> encryptionKey]

(***************************************************************************)
(* Three conditions must be fulfilled to decrypt data:                     *)
(*                                                                         *)
(*  (1) The encryption/decryption key must be from the same source         *)
(*  (2) If encrypted via public, must decrypt via private and vice-versa   *)
(*  (3) If a keyshare was used, the decryptor must have access to the      *)
(*      same partial keyshare as that which was used to encrypt            *)
(***************************************************************************)
Decrypt(data, decryptionKey) == 
    IF /\ decryptionKey.address = data.encryptionKey.address
       /\ decryptionKey.type = IF data.encryptionKey.type = "public_key" 
                               THEN "private_key"
                               ELSE IF data.encryptionKey.type = "private_key" 
                                    THEN "public_key"
                                    ELSE "" 
       /\ IF /\ "share" \in DOMAIN data.encryptionKey
             /\ "share" \in DOMAIN decryptionKey
          THEN decryptionKey.share = data.encryptionKey.share
          ELSE TRUE
    THEN data.encryptedData ELSE NULL 

IsEncrypted(data) == 
    \A f \in {"encryptedData", "encryptionKey"} : f \in DOMAIN data

=============================================================================
\* Modification History
\* Last modified Wed Mar 13 10:27:42 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
