import RelationalAlgebra.FOL.Relabel
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

namespace FOL

-- Query equivalence check (uses casting but only works when n = k)
def BoundedQuery.isQuery {n k : ℕ} (h : n ≤ k) (q : BoundedQuery n) (needle : BoundedQuery k) : Prop :=
  ite (n = k) (needle = q.castLE h) False

@[simp]
theorem BoundedQuery.isQuery.def_eq_hk {n k} {q : BoundedQuery n} (h : n ≤ k) (needle : BoundedQuery k) :
  isQuery (by simp [h]) q needle → n = k := by simp_all [isQuery]

@[simp]
theorem BoundedQuery.isQuery.def_eq {n hn} {q : BoundedQuery n} (needle : BoundedQuery n) :
  isQuery hn q needle ↔ needle = q := by simp_all [isQuery]

@[simp]
theorem BoundedQuery.isQuery.def_lt {n k} {q : BoundedQuery n} (h : n < k) (needle : BoundedQuery k) :
  isQuery (Nat.le_of_succ_le h) q needle ↔ False := by
    simp_all [isQuery]
    intro a
    subst a
    simp_all only [castLE_rfl]
    simp_all only [lt_self_iff_false]

-- Query containment check (uses casting but requires exact type match for needle)
def BoundedQuery.hasSubQuery {n k : ℕ} (h : n ≤ k) : (q : BoundedQuery n) → (needle : BoundedQuery k) → Prop
  | .tEq q t₁ t₂, needle => (tEq q t₁ t₂).isQuery h needle ∨ q.hasSubQuery h needle
  | .and q₁ q₂, needle => (and q₁ q₂).isQuery h needle ∨ q₁.hasSubQuery h needle ∨ q₂.hasSubQuery h needle
  | .ex q,      needle => dite (n + 1 ≤ k) (λ h' ↦ q.hasSubQuery h' needle) (λ _ ↦ (ex q).isQuery h needle)
  | q, needle   => q.isQuery h needle

@[simp]
theorem BoundedQuery.hasSubQuery.R_def {n k dbs rn t} (h : n ≤ k) (needle : BoundedQuery k) :
  hasSubQuery h (R dbs rn t) needle ↔ (R dbs rn t).isQuery h needle := by rfl

@[simp]
theorem BoundedQuery.hasSubQuery.tEq_def {n k t₁ t₂ q} (h : n ≤ k) (needle : BoundedQuery k) :
  hasSubQuery h (tEq q t₁ t₂) needle ↔ ((tEq q t₁ t₂).isQuery h needle ∨ hasSubQuery h q needle) := by rfl

@[simp]
theorem BoundedQuery.hasSubQuery.and_def (h : n ≤ k) (q₁ q₂ : BoundedQuery n) (needle : BoundedQuery k) :
  hasSubQuery h (and q₁ q₂) needle = ((and q₁ q₂).isQuery h needle ∨ hasSubQuery h q₁ needle ∨ hasSubQuery h q₂ needle) := rfl

@[simp]
theorem BoundedQuery.hasSubQuery.ex_def_le (h : n + 1 ≤ k) (q : BoundedQuery (n + 1)) (needle : BoundedQuery k) :
  hasSubQuery (Nat.le_of_succ_le h) (ex q) needle ↔ q.hasSubQuery h needle := by simp_all [hasSubQuery]

@[simp]
theorem BoundedQuery.hasSubQuery.ex_def_eq (q : BoundedQuery (n + 1)) (needle : BoundedQuery n) :
  hasSubQuery (Nat.le_refl n) (ex q) needle ↔ (ex q).isQuery (Nat.le_refl n) needle := by simp_all [hasSubQuery]

@[simp]
theorem BoundedQuery.hasSubQuery.ex_exists (q : BoundedQuery (n + 1)) (needle : BoundedQuery k)  (h'' : n + 1 ≤ k):
  (((h' : n + 1 = k) → q.isQuery h'' needle) ∧ ((h' : n < k) → q.hasSubQuery h' needle)) → hasSubQuery h (ex q) needle  := by
    intro a
    simp_all only [Nat.succ_eq_add_one, ex_def_le]

@[simp]
theorem BoundedQuery.hasSubQuery.exs_def (q : BoundedQuery n) (needle : BoundedQuery k) :
  hasSubQuery (by simp) (exs q) needle = hasSubQuery h q needle ∨ ¬k ≤ 0 := by
    induction n
    . aesop
    . aesop

@[simp]
theorem BoundedQuery.hasSubQuery.schema_def {k n hk} {needle : BoundedQuery k} {q : BoundedQuery n} (h : hasSubQuery hk q needle) :
  needle.schema ⊆ q.schema := by
    induction q with
    | R dbs rn t =>
      rename_i n'
      by_cases h' : n' = k
      . aesop
      . simp_all [isQuery]
    | tEq q _ _ =>
      simp_all only [forall_true_left, tEq_def, castLE, schema.tEq_def]
      cases h with
      | inl h_1 =>
        rename_i n' t₁ t₂ ih
        by_cases n' = k
        . aesop
        . simp_all [isQuery]
      | inr h_2 => simp_all only [forall_const]
    | and q₁ q₂ q₁_ih q₂_ih =>
      simp_all only [forall_true_left, and_def, schema.and_def]
      cases h with
      | inl h_1 =>
        rename_i n'
        by_cases n' = k
        . aesop
        . simp_all [isQuery]
      | inr h_2 =>
        cases h_2 with
        | inl h =>
          simp_all only [forall_const]
          exact Finset.union_subset_left (Finset.union_subset_union q₁_ih (Finset.empty_subset q₂.schema))
        | inr h_1 =>
          simp_all only [forall_const]
          exact Finset.union_subset_right (Finset.union_subset_union (Finset.empty_subset q₁.schema) q₂_ih)
    | ex q q_ih =>
        rename_i n'
        induction k
        . simp_all [hasSubQuery, isQuery]
          obtain ⟨left, right⟩ := h
          subst right left
          simp_all only [Nat.reduceAdd, castLE_rfl, subset_refl]
        . simp_all [hasSubQuery, isQuery]
          rename_i a
          split at a
          next h_1 =>
            split at h
            next h_2 => simp_all only [forall_const, forall_true_left, implies_true, imp_self]
            next
              h_2 =>
              simp_all only [add_le_iff_nonpos_right, zero_le, nonpos_iff_eq_zero, one_ne_zero, schema.ex_def,
                IsEmpty.forall_iff, implies_true, not_false_eq_true]
              simp_all only
              obtain ⟨left, right⟩ := h
              subst right left
              simp_all only [castLE_rfl, subset_refl]
          next h_1 =>
            split at h
            next h_2 =>
              simp_all only [forall_const, not_le, isEmpty_Prop, IsEmpty.forall_iff, schema.ex_def, and_imp,
                forall_true_left, forall_eq_apply_imp_iff]
            next
              h_2 =>
              simp_all only [add_le_iff_nonpos_right, zero_le, nonpos_iff_eq_zero, one_ne_zero, schema.ex_def,
                IsEmpty.forall_iff, not_le, isEmpty_Prop, Nat.add_eq_left, true_and, imp_self, implies_true,
                not_false_eq_true]
              obtain ⟨left, right⟩ := h
              subst left right
              simp_all only [castLE_rfl, subset_refl]
