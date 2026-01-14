import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Variable

open FOL FirstOrder Language RM Term

namespace FOL

variable {ρ α : Type}

/--
Syntax for a `BoundedQuery` given a database schema `dbs` and bound `n : ℕ`.
Similar to `ModelTheory.BoundedFormula`.
Note: Future work could remove this BoundedQuery intermediate layer,
      given the similarities with BoundedFormula in both syntax and semantics.
-/
inductive BoundedQuery (dbs : ρ → Finset α) : ℕ → Type
  | R {n} : (rn : ρ) → (Fin (dbs rn).card → (fol dbs).Term (α ⊕ Fin n)) → BoundedQuery dbs n
  | and {n} (q1 q2 : BoundedQuery dbs n): BoundedQuery dbs n
  | tEq {n} : (t₁ t₂ : (fol dbs).Term (α ⊕ Fin n)) → BoundedQuery dbs n
  | ex {n} (q : BoundedQuery dbs (n + 1)) : BoundedQuery dbs n
  | not {n} (q : BoundedQuery dbs n) : BoundedQuery dbs n

@[simp]
def BoundedQuery.or (q₁ q₂ : BoundedQuery dbs n) : BoundedQuery dbs n :=
  (q₁.not.and q₂.not).not

@[simp]
def BoundedQuery.all (q : BoundedQuery dbs (n + 1)) : BoundedQuery dbs n :=
  q.not.ex.not

/-- Syntax for a `Query` given a database schema `dbs` with bound `0`. Similar to `ModelTheory.Formula`. -/
abbrev Query (dbs : ρ → Finset α) := BoundedQuery dbs 0

variable {dbs : ρ → Finset α}

@[simp]
def BoundedQuery.exs : ∀ {n}, BoundedQuery dbs n → Query dbs
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

/-- `BoundedQuery` conversion to `BoundedFormula`. -/
@[simp]
def BoundedQuery.toFormula : (q : BoundedQuery dbs n) → (fol dbs).BoundedFormula α n
  | .R name vMap => Relations.boundedFormula (.R name) vMap
  | .tEq t₁ t₂ => .equal t₁ t₂
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_exs (q : BoundedQuery dbs n) : q.exs.toFormula = q.toFormula.exs := by
  induction n
  . rfl
  . rename_i a
    apply a
