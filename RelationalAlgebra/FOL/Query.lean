import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Variable

open FOL FirstOrder Language RM Term

namespace FOL

-- Query syntax
inductive BoundedQuery (dbs : DatabaseSchema) : ℕ → Type
  | R {n} : (rn : RelationName) → (Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) → BoundedQuery dbs n
  | and {n} (q1 q2 : BoundedQuery dbs n): BoundedQuery dbs n
  | tEq {n} : (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) → BoundedQuery dbs n
  | ex {n} (q : BoundedQuery dbs (n + 1)) : BoundedQuery dbs n
  | or {n} (q₁ q₂ : BoundedQuery dbs n) : BoundedQuery dbs n
  | not {n} (q : BoundedQuery dbs n) : BoundedQuery dbs n

abbrev Query (dbs : DatabaseSchema) := BoundedQuery dbs 0

@[simp]
def BoundedQuery.exs : ∀ {n}, BoundedQuery dbs n → Query dbs
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

@[simp]
def BoundedQuery.toFormula {n : ℕ} : (q : BoundedQuery dbs n) → fol.BoundedFormula Attribute n
  | .R name vMap => Relations.boundedFormula (fol.Rel dbs name) vMap
  | .tEq t₁ t₂ => .equal t₁ t₂
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .or q1 q2 => q1.toFormula ⊔ q2.toFormula
  | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_exs {n} (q : BoundedQuery dbs n) : q.exs.toFormula = q.toFormula.exs := by
  induction n
  . rfl
  . rename_i a
    apply a
