import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Variable

open FOL FirstOrder Language RM Term

namespace FOL

/-- Syntax for a `BoundedQuery` given a database schema `dbs` and bound `n : ℕ`. Similar to `ModelTheory.BoundedFormula`. -/
inductive BoundedQuery (dbs : String → Finset String) : ℕ → Type
  | R {n} : (rn : String) → (Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) → BoundedQuery dbs n
  | and {n} (q1 q2 : BoundedQuery dbs n): BoundedQuery dbs n
  | tEq {n} : (t₁ t₂ : (fol dbs).Term (String ⊕ Fin n)) → BoundedQuery dbs n
  | ex {n} (q : BoundedQuery dbs (n + 1)) : BoundedQuery dbs n
  | or {n} (q₁ q₂ : BoundedQuery dbs n) : BoundedQuery dbs n
  | not {n} (q : BoundedQuery dbs n) : BoundedQuery dbs n

/-- Syntax for a `Query` given a database schema `dbs` with bound `0`. Similar to `ModelTheory.Formula`. -/
abbrev Query (dbs : String → Finset String) := BoundedQuery dbs 0

@[simp]
def BoundedQuery.exs : ∀ {n}, BoundedQuery dbs n → Query dbs
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

/-- `BoundedQuery` conversion to `BoundeFormula`. -/
@[simp]
def BoundedQuery.toFormula : (q : BoundedQuery dbs n) → (fol dbs).BoundedFormula String n
  | .R name vMap => Relations.boundedFormula (fol.Rel name) vMap
  | .tEq t₁ t₂ => .equal t₁ t₂
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .or q1 q2 => q1.toFormula ⊔ q2.toFormula
  | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_exs (q : BoundedQuery dbs n) : q.exs.toFormula = q.toFormula.exs := by
  induction n
  . rfl
  . rename_i a
    apply a
