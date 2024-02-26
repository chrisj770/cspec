------------------------------ MODULE Common ------------------------------
EXTENDS Sequences, Integers

CONSTANTS 
    NumWorkers,
    NumRequesters,
    NumUSCs,
    NULL
    
VARIABLES
    Workers,
    Requesters,
    USCs,
    TSCs, 
    Time, 
    NextPubkey, 
    Storage
    
IsWorker(address) == 
    \E i \in 1..NumWorkers : Workers[i].address = address
    
IsRequester(address) == 
    \E i \in 1..NumRequesters : Requesters[i].address = address
    
GetWorker(address) == 
    CHOOSE i \in 1..NumWorkers : Workers[i].address = address
    
GetRequester(address) == 
    CHOOSE i \in 1..NumRequesters : Requesters[i].address = address

SendMessage(recipient, message) == 
    IF recipient = "TSC"
         THEN TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \union {message}]
    ELSE IF recipient = "USC"
         THEN USCs' = [USCs EXCEPT !.msgs = USCs.msgs \union {message}]
    ELSE IF IsRequester(recipient)
         THEN LET rid == GetRequester(recipient)
              IN Requesters' = [Requesters EXCEPT ![rid].msgs = Requesters[rid].msgs \union {message}]
    ELSE IF IsWorker(recipient) 
         THEN LET wid == GetWorker(recipient)
              IN Workers' = [Workers EXCEPT ![wid].msgs = Workers[wid].msgs \union {message}]
    ELSE FALSE
    
(***************************************************************************)
(* During registration, each user receive a pair of public/private         *)
(* encryption keys, which are used to encrypt/decrypt all instances of     *)
(* sensory data that gets exchanged with Database. These keys are          *)
(* represented as structs of the following format:                         *)
(*                                                                         *)
(* Key == [address |-> (encryptor_address),                                *)
(*            type |-> ("public" or "private")                             *)
(*           share |-> (Int or "NULL")]                                    *)
(*                                                                         *)
(* We also store each instance of encrypted data with the key used for     *)
(* encryption, as formatted below:                                         *)
(*                                                                         *)
(* EncryptedData == [data |-> (data),                                      *)
(*                    key |-> (key)]                                       *)
(*                                                                         *)
(* Any user "N" can encrypt data using their public key "Npk", or some     *)
(* share of the public key "Npk_1", "Npk_2", ..., "Npk_n". Once this       *)
(* occurs, the data can only be accessed by decrypting it via the          *)
(* corresponding private key "Nsk", or some share of the private key       *)
(* "Nsk_1", "Nsk_2", ..., "Nsk_n". These operations are represented via    *)
(* the methods below.                                                      *)
(***************************************************************************)
Encrypt(data, pk) == 
    [data |-> data, key |-> pk]

Decrypt(data, sk) == 
    IF /\ sk.address = data.key.address
       /\ sk.type = IF data.key.type = "public" THEN "private" ELSE FALSE 
       /\ sk.share = data.key.share
    THEN data.data ELSE NULL 

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 12:36:39 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
