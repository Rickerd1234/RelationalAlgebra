# Design Documentation

This document outlines the key design decisions made during the early phases of this project, particularly the proof-of-concept stage. It provides the rationale behind choices, the trade-offs considered, and the current status of each design decision.

---

## 📖 Theory

For the definitions we took a close look at the book [Principles of Databases](https://github.com/pdm-book/community), this book describes the relational model, relational algebra and first-order logic queries in great detail. For this reason, it seems like a great starting point for our formalization. We try to stay close to the definitions in the literature, to make sure our formalization is aligned with the theory. However, slight deviations might be used to enable simpler, more comprehensive or more abstract proofs.

---

## 🧩 Core Design Areas

### **Representation of Tuples and Relations**

#### ➤ Decision: Use of Partial Functions for Tuples

- **Implementation**:  

  ```lean
  abbrev Tuple := Attribute →. Value
  structure RelationInstance where
    schema : RelationSchema
    tuples : Set Tuple
    validSchema : ∀ t : Tuple, t ∈ tuples → t.Dom = schema
  ```

- **Rationale**:

  - Closely aligns with theoretical definitions in database literature.
  - Partial functions cleanly enforce schema constraints (tuple only defined on its relation’s schema).
  - More flexible than total functions or record-based representations.

- **Alternatives Considered**:

  - Dependent types (`Tuple : RelationSchema → Type`) — rejected due to type mismatch issues (e.g., schema order differences).
  - Use of `Option Value` and `isSome` checks — PFun is part of mathlib.

---

### **Bundled vs. Unbundled Relation Definitions**

#### ➤ Decision: Use Bundled `RelationInstance` Structures

- **Rationale**:

  - Avoids repeated schema parameters and dependent typing issues.
  - Simplifies type matching in proofs (e.g., `R ⋈ S = S ⋈ R`).
  - Encourages better encapsulation and avoids reliance on low-level coercions.

- **Alternatives Considered**:

  - Unbundled (tuple sets parameterized by schema) — caused significant type friction during join proofs.
  - Dependent types with coercions — manageable but cumbersome in larger proofs.

---

### **Schema Representation**

#### ➤ Decision: Schemas as Sets of Attributes (`Set Attribute`)

- **Rationale**:

  - Matches common textbook definitions.
  - Easy to check subset/superset conditions, schema equality.
  - Mathlib’s [Set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html) is a strong foundation.

---

### **Rename Operation Design**

#### ➤ Decision: Rename via Surjective Attribute Mapping

- **Rationale**:

  - Generalizes renaming across arbitrary schemas.
  - More abstract than single-attribute renaming; supports more realistic transformations.
  - Lean functions are well-suited for expressing this mapping.

---

### **Projection Semantics**

#### ➤ Decision: Projection as Schema Reduction

- **Approach**:

  - Define projection as selecting a sub-schema and mapping each tuple to a restricted domain.
  - Use partial function domain filtering to implement.

---
