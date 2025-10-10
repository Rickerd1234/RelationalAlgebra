import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

theorem Finset.empty.contra (s₁ : Finset Attribute) : (s₁ ≠ ∅) → (s₁ = ∅) → False := by simp

namespace FOL

def BoundedQuery.isWellTyped {n} : BoundedQuery dbs n → Prop
  | R _ _        => True
  | tEq q t₁ t₂  => q.isWellTyped ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂
  | and q₁ q₂    => q₁.isWellTyped ∧ q₂.isWellTyped
  | ex q         => q.isWellTyped
  | or q₁ q₂     => q₁.isWellTyped ∧ q₂.isWellTyped ∧ ∀t, q₁.hasSafeTerm t ↔ q₂.hasSafeTerm t
  | not q        => q.isWellTyped

@[simp]
theorem BoundedQuery.isWellTyped.R_def {rn n} {dbs : DatabaseSchema} {f : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)} :
  (R rn f).isWellTyped := by trivial

@[simp]
theorem BoundedQuery.isWellTyped.tEq_def {n} {q : BoundedQuery dbs n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} :
  (tEq q t₁ t₂).isWellTyped = (q.isWellTyped ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.and_def {n} {q₁ q₂ : BoundedQuery dbs n} :
  (and q₁ q₂).isWellTyped = (q₁.isWellTyped ∧ q₂.isWellTyped) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.ex_def {n} {q : BoundedQuery dbs (n + 1)} :
  (ex q).isWellTyped = q.isWellTyped := rfl

@[simp]
theorem BoundedQuery.isWellTyped.or_def {n} {q₁ q₂ : BoundedQuery dbs n} :
  (or q₁ q₂).isWellTyped = (q₁.isWellTyped ∧ q₂.isWellTyped ∧ ∀t, q₁.hasSafeTerm t ↔ q₂.hasSafeTerm t) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.not_def {n} {q : BoundedQuery dbs n} :
  (not q).isWellTyped = q.isWellTyped := rfl

@[simp]
theorem BoundedQuery.isWellTyped.exs_def {n} {q : BoundedQuery dbs n} :
  (exs q).isWellTyped = q.isWellTyped := by
    induction n with
    | zero => simp_all only [exs_0]
    | succ n' ih => exact ih

@[simp]
theorem BoundedQuery.isWellTyped.and_comm {n} {q₁ q₂ : BoundedQuery dbs n} (h : (and q₁ q₂).isWellTyped) :
  (and q₂ q₁).isWellTyped
    := by simp_all [Finset.union_comm]

@[simp]
theorem BoundedQuery.isWellTyped.and_from_both {n} {q₁ q₂ : BoundedQuery dbs n} (h₁ : q₁.isWellTyped) (h₂ : q₂.isWellTyped) :
  (and q₁ q₂).isWellTyped
    := by simp_all only [and_def, and_self]
