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
(*                        INTER-PROCESS COMMUNICATION                      *)
(*                                                                         *) 
(* The following operators represent a variety of message-related actions  *) 
(* that are available to any actor within the system. In practice, these   *)
(* would be replaced with HTTPS requests (or equivalent) sent to the       *)
(* recipient's corresponding web address (with public-key/address, if      *) 
(* the recipient is a smart contract).                                     *)
(***************************************************************************)
SendTSCMessage(message) == 
    TSCs' = [TSCs EXCEPT !.msgs = TSCs.msgs \union {message}]

SendUSCMessage(message) == 
    USCs' = [USCs EXCEPT !.msgs = USCs.msgs \union {message}]
    
SendStorageMessage(message) == 
    Storage' = [Storage EXCEPT !.msgs = Storage.msgs \union {message}]
    
SendRequesterMessage(recipient, message) == 
    /\ \E i \in 1..NumRequesters : Requesters[i].pk = recipient
    /\ LET rid == CHOOSE i \in 1..NumRequesters : Requesters[i].pk = recipient
       IN Requesters' = [Requesters EXCEPT ![rid].msgs = 
                            Requesters[rid].msgs \union {message}]
                            
SendWorkerMessage(recipient, message) == 
    /\ \E i \in 1..NumWorkers : Workers[i].pk = recipient
    /\ LET wid == CHOOSE i \in 1..NumWorkers : Workers[i].pk = recipient
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
(*                                                                         *)
(* NOTE: During registration, each user receives a pair of public/private  *)
(* keys, which can be used to encrypt/decrypt (1) key-shares sent between  *)
(* Workers/Requesters, and (2) sensory data exchanged between Workers and  *)
(* the database. These keys are represented as basic structure with the    *)
(* following format:                                                       *)
(*                                                                         *)
(* Key == [address |-> (encryptor_address),                                *)
(*            type |-> ("public_key" or "private_key")                     *)
(*           share |-> (Int)]                           <----OPTIONAL      *)
(*                                                                         *)
(* Upon encryption of data, we store the result as a structure containing  *)
(* (1) the encrypted data, and (2) the key utilized for encryption. This   *) 
(* allows us to determine whether another actor possesses sufficient       *)
(* information to decrypt the data (i.e. the corresponding private-key).   *)
(* Encrypted data is represented as follows:                               *)
(*                                                                         *)
(* EncryptedData == [encryptedData |-> (data),                             *)
(*                   encryptionKey |-> (key)]                              *)
(*                                                                         *)
(* Per the definition of a Paillier cryptosystem, any user "N" can encrypt *)
(* data using a public key "Npk", or some share of the public key "Npk_1", *)
(* "Npk_2", ..., "Npk_n". When this occurs, the data can only be decrypted *)
(* via the corresponding private key "Nsk", or the corresponding share of  *)
(* the private key "Nsk_1", "Nsk_2", ..., "Nsk_n", respectively. For more  *)
(* information, refer to online descriptions of the Paillier cryptosystem. *)
(***************************************************************************)

(***************************************************************************)
(* Encrypt: Represents encryption of data via key, outputs a structure     *)
(* containing the encrypted data and information on the encryption key.    *)
(***************************************************************************)
Encrypt(data, encryptionKey) == 
    [encryptedData |-> data, encryptionKey |-> encryptionKey]

(***************************************************************************)
(* Decrypt: Represents decryption of encrypted data via key, outputs       *) 
(* unencrypted data if successful or NULL otherwise.                       *)
(*                                                                         *)
(* The following conditions must be fulfilled to decrypt data:             *)
(*                                                                         *)
(*  (1) The encryption/decryption key must be from the same address.       *)
(*                                                                         *)
(*  (2) If encrypted via public key, the data must be decrypted via        *)
(*      private key (and vice-versa).                                      *)
(*                                                                         *)
(*  (3) If a partial keyshare was used for encryption, the decryptor       *)
(*      must have access to the corresponding share of the                 *) 
(*      decryption key.                                                    *) 
(*                                                                         *)
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

(***************************************************************************)
(* IsEncrypted: Checks whether data is encrypted, used primarily for       *) 
(* property verification.                                                  *)
(***************************************************************************) 
IsEncrypted(data) == 
    \A f \in {"encryptedData", "encryptionKey"} : f \in DOMAIN data

=============================================================================
\* Modification History
\* Last modified Fri Mar 22 10:15:58 CET 2024 by jungc
\* Created Thu Feb 22 10:44:28 CET 2024 by jungc
