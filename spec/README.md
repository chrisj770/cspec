# Spec Overview
This directory contains the raw TLA+ specification files for C-SPEC.  defines the exhaustive set of states, behaviors, and interactions upon which its respective component operates. Additionally, we define a set of behaviors common to one-or-more components (`Common.tla`), as well as a collection of properties and invariants to which each component adheres (`_Properties` files). 

As established in the BRPC protocol by _Wu et al._, this system consists of the following five categories of independent actors:

* __Workers__ — _External actors responsible for querying/accepting tasks, generating/submitting sensory data, and verifying Requester evaluation results. These entities perform the actual work required by each task, for which they receive rewards in cryptocurrency upon timely completion._

* __Requesters__ — _External actors responsible for posting tasks, distributing encrypted key-shares, and evaluating Worker submissions. These entities offer all information required to complete a task, as well as maintain responsibility for distributing the appropriate rewards upon completion._

* __Task Smart Contract (TSC)__ — _Blockchain contract responsible for registering posted tasks, accepting/rejecting Workers as task participants, accepting data submissions, and storing task-related information (e.g. state, deadlines, data hashes, evaluation results, etc.)._

* __User Smart Contract (USC)__ — _Blockchain contract responsible for registering external actors as Workers/Requesters, generating and distributing private/public keys, and storing user-related information (e.g. public/private keys, user-type, reputation, etc.)._

* __Decentralized Storage__ — _Blockchain-hosted database responsible for persisting encrypted sensory data and distributing it upon request._

In the following sections, we provide an in-depth overview of each category, as well as a visual diagram encapsulating the set of actions under all system conditions.

## Worker
![<Worker State Flowchart>](/../state_diagrams/Worker.png)

## Requester
![<Requester State Flowchart>](/../state_diagrams/Requester.png)

## Task Smart Contract (TSC)
![<TSC State Flowchart>](/../state_diagrams/TSC.png)

## User Smart Contract (USC)
![<USC State Flowchart>](/../state_diagrams/USC.png)

## Decentralized Storage
![<Storage State Flowchart>](/../state_diagrams/Storage.png)
