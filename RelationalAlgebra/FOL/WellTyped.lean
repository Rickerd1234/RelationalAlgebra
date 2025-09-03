import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.Subquery

open FOL FirstOrder Language RM Term

theorem Finset.empty.contra (s₁ : Finset Attribute) : (s₁ ≠ ∅) → (s₁ = ∅) → False := by simp

namespace FOL

def BoundedQuery.isWellTyped {n} : BoundedQuery n → Prop
  | R _ _ _      => True
  | tEq q t₁ t₂  => q.isWellTyped ∧ t₁.varFinsetLeft ∪ t₂.varFinsetLeft ⊆ q.schema
  | and q₁ q₂    => q₁.isWellTyped ∧ q₂.isWellTyped
  | ex q         => q.isWellTyped

@[simp]
theorem BoundedQuery.isWellTyped.R_def [folStruc] {dbs rn n} {t : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)} :
  (R dbs rn t).isWellTyped := by simp [isWellTyped]

@[simp]
theorem BoundedQuery.isWellTyped.tEq_def [folStruc] {n} {q : BoundedQuery n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} :
  (tEq q t₁ t₂).isWellTyped = (q.isWellTyped ∧ (t₁.varFinsetLeft ∪ t₂.varFinsetLeft ⊆ q.schema)) := rfl

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

-- @TODO: Check from here whether this is useful
theorem BoundedQuery.isWellTyped.subQuery_def [folStruc] {n} {q : BoundedQuery n} {sq : BoundedQuery k} {hk : n ≤ k} (h : q.isWellTyped) :
  q.hasSubQuery hk sq → (sq.isWellTyped)
    := by
      intro hs
      by_cases h' : n = k
      . induction q
        all_goals aesop
      . have z : n < k := by exact Nat.lt_of_le_of_ne hk h'
        induction q
        all_goals simp_all [isQuery]; try sorry


@[simp]
theorem BoundedQuery.isWellTyped.schema_eq_attributesInQuery [folStruc] {n} {q : BoundedQuery n} (h : q.isWellTyped) :
  q.schema = q.attributesInQuery
    := by
      induction q
      all_goals aesop
