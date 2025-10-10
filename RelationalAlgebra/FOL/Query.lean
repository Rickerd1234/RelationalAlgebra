import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Variable

open FOL FirstOrder Language RM Term

namespace FOL

-- Query syntax
inductive BoundedQuery (dbs : DatabaseSchema) : ℕ → Type
  | R {n} : (rn : RelationName) → (Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) → BoundedQuery dbs n
  | and {n} (q1 q2 : BoundedQuery dbs n): BoundedQuery dbs n
  | tEq {n} : (q : BoundedQuery dbs n) → (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) → BoundedQuery dbs n
  | ex {n} (q : BoundedQuery dbs (n + 1)) : BoundedQuery dbs n
  | or {n} (q₁ q₂ : BoundedQuery dbs n) : BoundedQuery dbs n
  | not {n} (q : BoundedQuery dbs n) : BoundedQuery dbs n

abbrev Query (dbs : DatabaseSchema) := BoundedQuery dbs 0

def BoundedQuery.isTEq {n dbs} : BoundedQuery dbs n → Prop
  | tEq _ _ _ => True
  | _ => False

@[simp]
theorem BoundedQuery.isTEq_rel {n} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  (R rn vMap).isTEq = False := by rfl

@[simp]
theorem BoundedQuery.isTEq_tEq {n} {q : BoundedQuery dbs n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} : (tEq q t₁ t₂).isTEq = True := rfl

@[simp]
theorem BoundedQuery.isTEq_and {n} (q₁ q₂ : BoundedQuery dbs n) : (q₁.and q₂).isTEq = False := rfl

@[simp]
theorem BoundedQuery.isTEq_ex {n} (q : BoundedQuery dbs (n + 1)) : q.ex.isTEq = False := rfl

theorem BoundedQuery.isTEq_or {n} (q₁ q₂ : BoundedQuery dbs n) : (q₁.or q₂).isTEq = False := rfl

theorem BoundedQuery.isTEq_not {n} (q : BoundedQuery dbs n) : q.not.isTEq = False := rfl

@[simp]
theorem BoundedQuery.isTEq_exists {n} {q : BoundedQuery dbs n} : q.isTEq ↔ ∃q' t₁ t₂, q = tEq q' t₁ t₂  := by
  simp_all [isTEq]
  split
  next x t₁ t₂ => simp_all only [tEq.injEq, exists_and_left, exists_eq', and_true, true_iff]
  next x x_1 => simp_all only [imp_false, exists_false]

def BoundedQuery.exs : ∀ {n}, BoundedQuery dbs n → Query dbs
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

@[simp]
theorem BoundedQuery.exs_0 (q : BoundedQuery dbs 0) : q.exs = q := rfl

def BoundedQuery.toFormula {n : ℕ} : (q : BoundedQuery dbs n) → fol.BoundedFormula Attribute n
  | .R name vMap => Relations.boundedFormula (fol.Rel dbs name) vMap
  | .tEq q t₁ t₂ => q.toFormula ⊓ (.equal t₁ t₂)
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .or q1 q2 => q1.toFormula ⊔ q2.toFormula
  | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_rel {n} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  (R rn vMap).toFormula = (Relations.boundedFormula (fol.Rel dbs rn) vMap) := by
    rfl

@[simp]
theorem BoundedQuery.toFormula_tEq {n} {q : BoundedQuery dbs n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} : (tEq q t₁ t₂).toFormula = q.toFormula ⊓ .equal t₁ t₂ := by
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
