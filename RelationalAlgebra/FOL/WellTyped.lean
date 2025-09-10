import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

theorem Finset.empty.contra (s₁ : Finset Attribute) : (s₁ ≠ ∅) → (s₁ = ∅) → False := by simp

namespace FOL

def BoundedQuery.isWellTyped {n} : BoundedQuery n → Prop
  | R _ _ _      => True
  | tEq q t₁ t₂  => q.isWellTyped ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂
  | and q₁ q₂    => q₁.isWellTyped ∧ q₂.isWellTyped
  | ex q         => q.isWellTyped

@[simp]
theorem BoundedQuery.isWellTyped.R_def [folStruc] {dbs rn n} {f : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)} :
  (R dbs rn f).isWellTyped := by simp [isWellTyped]

@[simp]
theorem BoundedQuery.isWellTyped.tEq_def [folStruc] {n} {q : BoundedQuery n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} :
  (tEq q t₁ t₂).isWellTyped = (q.isWellTyped ∧ q.hasSafeTerm t₁ ∧ q.hasSafeTerm t₂) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.and_def [folStruc] {n} {q₁ q₂ : BoundedQuery n} :
  (and q₁ q₂).isWellTyped = (q₁.isWellTyped ∧ q₂.isWellTyped) := rfl

@[simp]
theorem BoundedQuery.isWellTyped.ex_def [folStruc] {n} {q : BoundedQuery (n + 1)} :
  (ex q).isWellTyped = q.isWellTyped := rfl

@[simp]
theorem BoundedQuery.isWellTyped.exs_def [folStruc] {n} {q : BoundedQuery n} :
  (exs q).isWellTyped = q.isWellTyped := by
    induction n with
    | zero => simp_all only [exs_0]
    | succ n' ih => exact ih

@[simp]
theorem BoundedQuery.isWellTyped.and_comm [folStruc] {n} {q₁ q₂ : BoundedQuery n} (h : (and q₁ q₂).isWellTyped) :
  (and q₂ q₁).isWellTyped
    := by simp_all [Finset.union_comm]

@[simp]
theorem BoundedQuery.isWellTyped.and_from_both [folStruc] {n} {q₁ q₂ : BoundedQuery n} (h₁ : q₁.isWellTyped) (h₂ : q₂.isWellTyped) :
  (and q₁ q₂).isWellTyped
    := by simp_all only [and_def, and_self]
