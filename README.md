# Formalizing Relational Algebra and its Equivalence to First-Order Logic in Lean

This repository contains the formalization code and supporting materials for my thesis project: **"Formalizing the Relational Algebra and Its Equivalence to First-Order Logic in the Lean Proof Assistant"**, conducted at Eindhoven University of Technology.

## 📚 Overview

Relational Algebra (RA) is the theoretical foundation of SQL and a cornerstone of database theory. It has a deep and well-understood connection to First-Order Logic (FOL), with known equivalences under active domain semantics.

This project formalizes:

- The core constructs of Relational Algebra (e.g. selection, projection, join, union, difference, renaming).
- A corresponding fragment of First-Order Logic with active domain semantics.
- The expressive equivalence between RA and FOL under this interpretation.

The formalization is developed in [Lean 4](https://leanprover.github.io), using its dependent type theory framework and the [mathlib4](https://github.com/leanprover-community/mathlib4) library where possible.

## ✅ Goals

- 🕑 Formalize SPJR algebra.
- 🕑 Formalize SPJRU algebra.
- 🕑 Formalize complete relational algebra.
- 🕑 Formalize equivalent fragments of FOL.
- 🕑 Prove equivalence theorems between RA and FOL expressions.
- 🔄 Ensure reusable and well-documented Lean definitions.
- 🧩 Contribute to or align with `mathlib4` standards.

## 🧠 Design Rationale

The design decisions behind the formalization — such as how tuples, schemas, and relational operations are represented in Lean — are documented in the [`Design.md`](./Design.md) file. This includes:

- Key trade-offs (e.g., bundled vs. unbundled representations)
- Justification for using partial functions and specific Lean constructs

Reading `Design.md` is recommended if you're contributing to the codebase or want to understand the reasoning behind implementation choices.

---
