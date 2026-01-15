# Formalizing Relational Algebra and its Equivalence to First-Order Logic in Lean

This repository contains the formalization code and supporting materials for my thesis project: **"Formalizing the Relational Algebra and Its Equivalence to First-Order Logic in the Lean Proof Assistant"**, conducted at Eindhoven University of Technology.

## 📚 Overview

Relational Algebra (RA) is the theoretical foundation of SQL and a cornerstone of database theory. It has a deep and well-understood connection to First-Order Logic (FOL), with known equivalences under active domain semantics.

This project formalizes:

- The core constructs of Relational Algebra (i.e. selection, projection, join, renaming, union, difference).
- A corresponding fragment of First-Order Logic with active domain semantics.
- The expressive equivalence between RA and FOL under this interpretation.

The formalization is developed in [Lean 4](https://leanprover.github.io), using its dependent type theory framework and the [mathlib4](https://github.com/leanprover-community/mathlib4) library where possible.

## ✅ Goals

- ✅ Formalize relational algebra.
- ✅ Formalize equivalent fragments of FOL.
- ✅ Prove equivalence theorems between RA and FOL expressions.
- 🔄 Ensure reusable and well-documented Lean definitions.

---
