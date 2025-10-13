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

def BoundedQuery.exs : ∀ {n}, BoundedQuery dbs n → Query dbs
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

@[simp]
theorem BoundedQuery.exs_0 (q : BoundedQuery dbs 0) : q.exs = q := rfl

def BoundedQuery.toFormula {n : ℕ} : (q : BoundedQuery dbs n) → fol.BoundedFormula Attribute n
  | .R name vMap => Relations.boundedFormula (fol.Rel dbs name) vMap
  | .tEq t₁ t₂ => .equal t₁ t₂
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .or q1 q2 => q1.toFormula ⊔ q2.toFormula
  | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_rel {n} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  (R rn vMap).toFormula = (Relations.boundedFormula (fol.Rel dbs rn) vMap) := by
    rfl

@[simp]
theorem BoundedQuery.toFormula_tEq {n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} : (tEq t₁ t₂ : BoundedQuery dbs n).toFormula = .equal t₁ t₂ := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_and {n} (q₁ q₂ : BoundedQuery dbs n) : (q₁.and q₂).toFormula = q₁.toFormula ⊓ q₂.toFormula := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_ex {n} (q : BoundedQuery dbs (n + 1)) : q.ex.toFormula = q.toFormula.ex := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_or {n} (q₁ q₂ : BoundedQuery dbs n) : (q₁.or q₂).toFormula = q₁.toFormula ⊔ q₂.toFormula := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_not {n} (q : BoundedQuery dbs n) : q.not.toFormula = q.toFormula.not := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_exs {n} (q : BoundedQuery dbs n) : q.exs.toFormula = q.toFormula.exs := by
  induction n
  . rfl
  . rename_i a
    apply a
