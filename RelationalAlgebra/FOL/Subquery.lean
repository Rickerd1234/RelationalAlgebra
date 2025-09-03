import RelationalAlgebra.FOL.Relabel
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

namespace FOL

def BoundedQuery.hasSubQuery {n k : ℕ} (h : n ≤ k) : (q : BoundedQuery n) → (needle : BoundedQuery k) → Prop
  | .and q₁ q₂, needle => q₁.hasSubQuery h needle ∨ q₂.hasSubQuery h needle
  | .ex q,      needle => dite (n + 1 ≤ k) (λ h' ↦ q.hasSubQuery h' needle) (λ _ ↦ False)
  | q, needle   => needle = q.castLE h

@[simp]
theorem BoundedQuery.hasSubQuery.R_def {n k dbs rn t} (h : n ≤ k) (needle : BoundedQuery k) :
  hasSubQuery h (R dbs rn t) needle = (needle = (R dbs rn t).castLE h) := rfl

@[simp]
theorem BoundedQuery.hasSubQuery.tEq_def {n k t₁ t₂} (h : n ≤ k) (needle : BoundedQuery k) :
  hasSubQuery h (tEq t₁ t₂) needle = (needle = (tEq t₁ t₂).castLE h) := rfl

@[simp]
theorem BoundedQuery.hasSubQuery.and_def (h : n ≤ k) (q₁ q₂ : BoundedQuery n) (needle : BoundedQuery k) :
  hasSubQuery h (and q₁ q₂) needle = (hasSubQuery h q₁ needle ∨ hasSubQuery h q₂ needle) := rfl

@[simp]
theorem BoundedQuery.hasSubQuery.ex_def_le (h : n + 1 ≤ k) (q : BoundedQuery (n + 1)) (needle : BoundedQuery k) :
  hasSubQuery (Nat.le_of_succ_le h) (ex q) needle = q.hasSubQuery h needle := by simp_all [hasSubQuery]

@[simp]
theorem BoundedQuery.hasSubQuery.ex_def_not_le (h : n ≤ k) (h' : ¬(n + 1) ≤ k) (q : BoundedQuery (n + 1)) (needle : BoundedQuery k) :
  hasSubQuery h (ex q) needle = False := by simp_all [hasSubQuery]

@[simp]
theorem BoundedQuery.hasSubQuery.ex_hk {n k hk} (q : BoundedQuery (n + 1)) (needle : BoundedQuery k) (h' : hasSubQuery hk (ex q) needle) :
  n + 1 ≤ k := by
    simp_all [hasSubQuery];
    obtain ⟨w, h⟩ := h'
    simp_all only

@[simp]
theorem BoundedQuery.hasSubQuery.ex_exists (q : BoundedQuery (n + 1)) (needle : BoundedQuery k) (h' : hasSubQuery h (ex q) needle) :
  q.hasSubQuery (ex_hk q needle h') needle := by
    induction k
    . exact False.elim h'
    . exact (ex_def_le (ex_hk q needle h') q needle).mp h'

@[simp]
theorem BoundedQuery.hasSubQuery.exs_def (q : BoundedQuery n) (needle : BoundedQuery k) :
  hasSubQuery (by simp) (exs q) needle = hasSubQuery h q needle ∨ ¬k ≤ 0 := by
    induction n
    . aesop
    . aesop

@[simp]
theorem BoundedQuery.hasSubQuery.schema_def [folStruc] {needle : BoundedQuery k} {q : BoundedQuery n} (h : hasSubQuery hk q needle) :
  needle.schema ⊆ q.schema := by
    induction q with
    | R _ _ _ => simp_all [schema, attributesInQuery, Relations.boundedFormula]
    | tEq _ _ => simp_all
    | and q₁ q₂ q₁_ih q₂_ih =>
      simp [hasSubQuery] at h;
      simp_all only [forall_true_left, schema.and_def]
      cases h with
      | inl h_1 =>
        simp_all only [forall_const]
        exact Finset.union_subset_left (Finset.union_subset_union q₁_ih (Finset.empty_subset q₂.schema))
      | inr h_2 =>
        simp_all only [forall_const]
        exact Finset.union_subset_right (Finset.union_subset_union (Finset.empty_subset q₁.schema) q₂_ih)
    | ex q q_ih => simp_all [ex_hk q needle h]
