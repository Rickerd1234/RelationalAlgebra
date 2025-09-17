import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

theorem Finset.empty.contra (s₁ : Finset Attribute) : (s₁ ≠ ∅) → (s₁ = ∅) → False := by simp

namespace FOL

def BoundedQuery.isWellTyped {n} (dbs : DatabaseSchema) : BoundedQuery n → Prop
  | R dbs' _ _   => dbs' = dbs
  | tEq q t₁ t₂  => q.isWellTyped dbs ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂
  | and q₁ q₂    => q₁.isWellTyped dbs ∧ q₂.isWellTyped dbs
  | ex q         => q.isWellTyped dbs

@[simp]
theorem BoundedQuery.isWellTyped.R_def {dbs rn n} {f : Fin (Finset.card (dbs' rn)) → fol.Term (Attribute ⊕ Fin n)} :
  (R dbs' rn f).isWellTyped dbs ↔ dbs' = dbs := by rfl

@[simp]
theorem BoundedQuery.isWellTyped.tEq_def {n} {q : BoundedQuery n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} :
  (tEq q t₁ t₂).isWellTyped dbs = (q.isWellTyped dbs ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.and_def {n} {q₁ q₂ : BoundedQuery n} :
  (and q₁ q₂).isWellTyped dbs = (q₁.isWellTyped dbs ∧ q₂.isWellTyped dbs) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.ex_def {n} {q : BoundedQuery (n + 1)} :
  (ex q).isWellTyped dbs = q.isWellTyped dbs := rfl

@[simp]
theorem BoundedQuery.isWellTyped.exs_def {n} {q : BoundedQuery n} :
  (exs q).isWellTyped dbs = q.isWellTyped dbs := by
    induction n with
    | zero => simp_all only [exs_0]
    | succ n' ih => exact ih

@[simp]
theorem BoundedQuery.isWellTyped.and_comm {n} {q₁ q₂ : BoundedQuery n} (h : (and q₁ q₂).isWellTyped dbs) :
  (and q₂ q₁).isWellTyped dbs
    := by simp_all [Finset.union_comm]

@[simp]
theorem BoundedQuery.isWellTyped.and_from_both {n} {q₁ q₂ : BoundedQuery n} (h₁ : q₁.isWellTyped dbs) (h₂ : q₂.isWellTyped dbs) :
  (and q₁ q₂).isWellTyped dbs
    := by simp_all only [and_def, and_self]
