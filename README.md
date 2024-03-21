 # C-SPEC

This repository contains __C-SPEC__, a formal TLA+ specification of a decentralized crowdsourcing system implemented on the Ethereum blockchain. It was developed at the University of Copenhagen for a (currently unpublished) master's thesis titled "_C-SPEC: Formal Specification of Blockchain-based Crowdsourcing Systems_".

## Background

C-SPEC is based on the BRPC architecture proposed by _Wu et al._ in the 2022 research paper "[_Blockchain-Based Reliable and Privacy-Aware Crowdsourcing With Truth and Fairness Assurance_](https://ieeexplore.ieee.org/document/9490332)". In their paper, the authors describe an automated system consisting of "Workers" and "Requesters" that interact with several Ethereum-based Smart Contracts to accomplish crowdsourcing tasks in exchange for cryptocurrency rewards. This system utilizes a Confidence-Aware Truth Discovery (CATD) algorithm and multi-stage verification approach to guarantee qualities of fairness, security, and reliability to all parties. 

In brief, C-SPEC attempts to generalize the BRPC protocol by offering a comprehensive specification of all interactions between "_Workers_", "_Requesters_", "_Task Smart Contracts_" (TSCs), "_User Smart Contracts_" (USCs), and a decentralized database. By standardizing this process in TLA+, we can guarantee certain properties of _safety_ and _liveness_ for any future blockchain-based crowdsourcing implementations based on our spec. This allows researchers to focus upon improving Truth Discovery algorithms, rather than re-assessing the safety/liveness of their systems with each new implementation.

## Contents

This repository is partitioned into the following sections:

- [cspec/spec](/spec) — Contains the TLA+ specification of C-SPEC.
- [cspec/state_diagrams](/state_diagrams) — Contains state diagrams for each actor developed in _draw.io_, saved as XML files.

Note that, as new requirements are constantly being added, the contents of each partition may undergo re-organization or significant modification.