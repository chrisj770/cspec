------------------------------ MODULE Common ------------------------------
EXTENDS Sequences, Integers

CONSTANTS 
    NumWorkers,
    NumRequesters,
    NumUSCs,
    NULL, 
    MaxTime
    
VARIABLES
    Workers,
    Requesters,
    USCs,
    TSCs, 
    Time, 
    NextUnique, 
    Storage
    
IsWorker(public_key) == 
    \E i \in 1..NumWorkers : Workers[i].pk = public_key
    
IsRequester(public_key) == 
    \E i \in 1..NumRequesters : Requesters[i].pk = public_key
    
GetWorker(public_key) == 
    CHOOSE i \in 1..NumWorkers : Workers[i].pk = public_key
    
GetRequester(public_key) == 
    CHOOSE i \in 1..NumRequesters : Requesters[i].pk = public_key

SendMessage(recipient, message) == 
    IF recipient.address = "TSC"
         THEN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \union {message}]
    ELSE IF recipient.address = "USC"
         THEN USCs' = [USCs EXCEPT !.msgs = USCs.msgs \union {message}]
    ELSE IF recipient.address = "STORAGE"
         THEN Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {message}]
    ELSE IF IsRequester(recipient)
         THEN LET rid == GetRequester(recipient)
              IN Requesters' = [Requesters EXCEPT ![rid].msgs = 
                                Requesters[rid].msgs \union {message}]
    ELSE IF IsWorker(recipient) 
         THEN LET wid == GetWorker(recipient)
              IN Workers' = [Workers EXCEPT ![wid].msgs =
                             Workers[wid].msgs \union {message}]
    ELSE FALSE
  
(* 
\* (TODO: Might need this for later) 
SendWorkerBroadcast(recipientSet, message) == 
    Workers' = [i \in 1..NumWorkers |-> [Workers[i] EXCEPT
                 !.msgs = IF Workers[i].pk \in recipientSet
                          THEN Workers[i].msgs \union {message}
                          ELSE Workers[i].msgs]]
*)
    
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

=============================================================================
\* Modification History
\* Last modified Sat Mar 02 11:49:39 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
