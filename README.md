# SMT Dataset Project

**Author:** Guofu Tang

**Advisor:** Prof. Hongce Zhang

**Institution:** HKUST(GZ)

## 📌 Overview

This project aims to **translate SMT-COMP benchmark problems into Lean 4 formalizations**, creating a structured dataset for research on automated theorem proving with Large Language Models (LLMs).

The long-term goal is to investigate whether **LLMs can learn to generate Lean proofs** for SMT-style problems, using a dataset of human-written Lean 4 formalizations as supervised training material.

This repository contains:

* **SMT/** – Original SMT-LIB2 benchmark problems (filtered QF_BV subset)
* **SMTDATASETPROJECT/** – Lean 4 formalizations corresponding to SMT problems
* Project configuration files for Lean 4 + Mathlib
* GitHub workflow files for CI support


## 📁 Repository Structure
```
.
├── SMT/                     # Original SMT-LIB benchmark files
│   ├── README.md
│   └── ...
│
├── SMTDATASETPROJECT/       # Lean 4 formalizations
│   ├── Basic.lean
│   ├── ...
│
├── lean-toolchain           # Lean version specification
├── lakefile.toml            # Lake project configuration
├── lake-manifest.json
├── .github/workflows/       # CI for Lean
└── README.md

```
## Research Motivation

The project explores:

1. **Formalizing SMT logic inside Lean 4**

   * Especially QF_BV (quantifier-free bitvector logic).
   * Creating Lean theorems mirroring SMT constraints.

2. **Building a parallel dataset**

   * `(SMT problem) → (Lean theorem + Lean proof)`
   * Designed for training LLMs.

3. **Using LLMs to generate Lean proofs**

   * Teacher-forcing approach:
     Human writes initial dataset →
     LLM learns proof patterns →
     LLM attempts new SMT problems →
     Lean kernel verifies correctness.

The dataset may contribute to future work on:

* Proof automation
* Lean-based SMT solving
* Verified LLM proof generation




