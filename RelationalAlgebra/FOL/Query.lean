import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Variable

open FOL FirstOrder Language RM Term

namespace FOL

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n} : (dbs : DatabaseSchema) → (rn : RelationName) → (Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) → BoundedQuery n
  | tEq {n} : (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n
  -- | all {n} (q : BoundedQuery (n + 1)) : BoundedQuery n
  -- | not {n} (q : BoundedQuery n) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedQuery.isTEq {n} : BoundedQuery n → Prop
  | tEq _ _ => True
  | _ => False

@[simp]
theorem BoundedQuery.isTEq_rel {n} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  (R dbs rn vMap).isTEq = False := by rfl

@[simp]
theorem BoundedQuery.isTEq_tEq {n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} : (tEq t₁ t₂).isTEq = True := rfl

@[simp]
theorem BoundedQuery.isTEq_and {n} (q₁ q₂ : BoundedQuery n) : (q₁.and q₂).isTEq = False := rfl

@[simp]
theorem BoundedQuery.isTEq_ex {n} (q : BoundedQuery (n + 1)) : q.ex.isTEq = False := rfl

@[simp]
theorem BoundedQuery.isTEq_exists {n} {q : BoundedQuery n} (h : q.isTEq) : ∃ t₁ t₂, q = tEq t₁ t₂  := by
  simp_all [isTEq];
  split at h
  next x t₁ t₂ => simp_all only [tEq.injEq, exists_and_left, exists_eq', and_true]
  next x x_1 => simp_all only [implies_true]

def BoundedQuery.exs : ∀ {n}, BoundedQuery n → Query
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

@[simp]
theorem BoundedQuery.exs_0 (q : BoundedQuery 0) : q.exs = q := rfl

def BoundedQuery.toFormula {n : ℕ} : (q : BoundedQuery n) → fol.BoundedFormula Attribute n
  | .R dbs name vMap => Relations.boundedFormula (fol.Rel dbs name) vMap
  | .tEq t₁ t₂ => .equal t₁ t₂
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  -- | .all q => .all q.toFormula
  -- | .not q => .not q.toFormula

@[simp]
theorem BoundedQuery.toFormula_rel {n} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  (R dbs rn vMap).toFormula = (Relations.boundedFormula (fol.Rel dbs rn) vMap) := by
    rfl

@[simp]
theorem BoundedQuery.toFormula_tEq {n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} : (tEq t₁ t₂).toFormula = .equal t₁ t₂ := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_and {n} (q₁ q₂ : BoundedQuery n) : (q₁.and q₂).toFormula = q₁.toFormula ⊓ q₂.toFormula := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_ex {n} (q : BoundedQuery (n + 1)) : q.ex.toFormula = q.toFormula.ex := by
  rfl

@[simp]
theorem BoundedQuery.toFormula_exs {n} (q : BoundedQuery n) : q.exs.toFormula = q.toFormula.exs := by
  induction n
  . rfl
  . rename_i a
    apply a
