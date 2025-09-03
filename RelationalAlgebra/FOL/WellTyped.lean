import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.SubQuery

open FOL FirstOrder Language RM Term

theorem Finset.empty.contra (s₁ : Finset Attribute) : (s₁ ≠ ∅) → (s₁ = ∅) → False := by simp

namespace FOL

def BoundedQuery.isWellTypedSubTEq {n} (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) (rs : RelationSchema) : Prop :=
   t₁.varFinsetLeft ∪ t₂.varFinsetLeft ⊆ rs

@[simp]
theorem BoundedQuery.isWellTypedSubTEq.tEq_def [folStruc] {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} {rs : RelationSchema} :
  BoundedQuery.isWellTypedSubTEq t₁ t₂ rs ↔ t₁.varFinsetLeft ∪ t₂.varFinsetLeft ⊆ rs := by rfl

def BoundedQuery.isWellTypedRec {n} : RelationSchema → BoundedQuery n → Prop
  | _,  R _ _ _     => True
  | rs, .tEq t₁ t₂  => BoundedQuery.isWellTypedSubTEq t₁ t₂ rs
  | _,  .and q₁ q₂  => q₁.isWellTypedRec (q₂.schema) ∧ q₂.isWellTypedRec (q₁.schema)
  | rs, .ex q       => q.isWellTypedRec rs

@[simp]
theorem BoundedQuery.isWellTypedRec.R_def [folStruc] {dbs rn n} {t : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)} {rs : RelationSchema} :
  (R dbs rn t).isWellTypedRec rs := by simp [isWellTypedRec]

@[simp]
theorem BoundedQuery.isWellTypedRec.tEq_def [folStruc] {n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} {rs : RelationSchema} :
  (tEq t₁ t₂).isWellTypedRec rs = BoundedQuery.isWellTypedSubTEq t₁ t₂ rs := rfl

@[simp]
theorem BoundedQuery.isWellTypedRec.and_def [folStruc] {n} {q₁ q₂ : BoundedQuery n} {rs : RelationSchema} :
  (and q₁ q₂).isWellTypedRec rs = (q₁.isWellTypedRec q₂.schema ∧ q₂.isWellTypedRec q₁.schema) := rfl

@[simp]
theorem BoundedQuery.isWellTypedRec.ex_def [folStruc] {n} {q : BoundedQuery (n + 1)} {rs : RelationSchema} :
  (ex q).isWellTypedRec rs = q.isWellTypedRec rs := rfl

@[simp]
theorem BoundedQuery.isWellTypedRec.exs_def [folStruc] {n} {q : BoundedQuery n} {rs : RelationSchema} :
  (exs q).isWellTypedRec rs = q.isWellTypedRec rs := by
    induction n with
    | zero => simp_all only [exs_0]
    | succ n' ih => exact ih

@[simp]
theorem BoundedQuery.isWellTypedRec_sub [folStruc] {n} {q : BoundedQuery n} {rs rs' : RelationSchema} (h₁ : rs' ⊆ rs) (h₂ : q.isWellTypedRec rs'):
  q.isWellTypedRec rs := by
    induction q with
    | R _ _ _ => simp_all only [isWellTypedRec.R_def]
    | tEq t₁ t₂ => simp_all only [isWellTypedRec.tEq_def, isWellTypedSubTEq.tEq_def]; exact fun ⦃a⦄ h' ↦ h₁ (h₂ h')
    | and q₁ q₂ q₁_ih q₂_ih => simp_all only [isWellTypedRec.and_def, and_self]
    | ex q q_ih => simp_all only [isWellTypedRec.ex_def]

@[simp]
theorem BoundedQuery.isWellTypedRec_empty [folStruc] {n} {q : BoundedQuery n} {rs : RelationSchema} (h : q.isWellTypedRec ∅):
  q.isWellTypedRec rs := isWellTypedRec_sub (by simp) h

def BoundedQuery.isWellTyped {n} : BoundedQuery n → Prop := BoundedQuery.isWellTypedRec ∅

@[simp]
theorem BoundedQuery.isWellTyped_def [folStruc] {n} {q : BoundedQuery n} :
  q.isWellTyped ↔ q.isWellTypedRec ∅ := by simp_all [isWellTyped];

@[simp]
theorem BoundedQuery.isWellTyped.tEq_def_inVar [folStruc] {n} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} :
  (tEq t₁ t₂).isWellTyped ↔ (∃i₁, t₁ = inVar i₁) ∧ (∃i₂, t₂ = inVar i₂)
    := by
      apply Iff.intro
      . intro h
        simp_all only [isWellTyped, isWellTypedRec.tEq_def, isWellTypedSubTEq.tEq_def,
          Finset.subset_empty, Finset.union_eq_empty]
        unfold varFinsetLeft at h
        split at h
        next x i =>
          split at h
          next x_1 i_1 =>
            exact False.elim (Finset.empty.contra ({i} ∪ {i_1}) (by simp) (by simp [h]))
          next x_1 _i =>
            exact False.elim (Finset.empty.contra {i} (by simp) (by simp [h]))
          next x_1 l _f ts =>
            exact False.elim (folStruc_empty_fun _f)
        next x _i =>
          split at h
          next x_1 i_1 =>
            exact False.elim (Finset.empty.contra (∅ ∪ {i_1}) (by simp) (by simp [h]))
          next x_1 _i =>
            simp_all only [Finset.union_idempotent]
            apply And.intro
            · apply Exists.intro
              · rfl
            · apply Exists.intro
              · rfl
          next x_1 l _f ts =>
            exact False.elim (folStruc_empty_fun _f)
        next x l _f ts =>
          exact False.elim (folStruc_empty_fun _f)
      . intro h
        obtain ⟨left, right⟩ := h
        obtain ⟨w, h⟩ := left
        obtain ⟨w_1, h_1⟩ := right
        subst h h_1
        simp_all [isWellTyped]
        exact And.intro rfl rfl

@[simp]
theorem BoundedQuery.isWellTyped.and_comm [folStruc] {n} {q₁ q₂ : BoundedQuery n} (h : (and q₁ q₂).isWellTyped) :
  (and q₂ q₁).isWellTyped
    := by simp_all [Finset.union_comm]

@[simp]
theorem BoundedQuery.isWellTyped.and_from_both [folStruc] {n} {q₁ q₂ : BoundedQuery n} (h₁ : q₁.isWellTyped) (h₂ : q₂.isWellTyped) :
  (and q₁ q₂).isWellTyped
    := by simp_all only [isWellTyped_def, Finset.subset_empty, isWellTypedRec.and_def,
      isWellTypedRec_empty, and_self, isWellTypedRec_sub]

@[simp]
theorem BoundedQuery.isWellTyped.and_from_sub [folStruc] {n} {q₁ q₂ : BoundedQuery n} (h₁ : q₁.isWellTyped) (h₂ : q₂.attributesInQuery ⊆ q₁.schema) (h₃ : q₂.isTEq) :
  (and q₁ q₂).isWellTyped
    := by
      aesop



-- @TODO: Check from here whether this is useful
theorem BoundedQuery.isWellTypedRec.subQuery_def [folStruc] {n} {q : BoundedQuery n} {sq : BoundedQuery k} {hk : n ≤ k} (h : q.isWellTypedRec q.schema) :
  q.hasSubQuery hk sq → (sq.isWellTypedRec ∅)
    := by
      intro hs
      induction q with
      | R dbs rn t =>
        subst hs
        simp_all
      | tEq t₁ t₂ =>
        subst hs
        simp_all
      | and q₁ q₂ q₁_ih q₂_ih =>
        simp_all only [isWellTyped_def, Finset.subset_empty, forall_true_left, isWellTypedRec.and_def,
          hasSubQuery.and_def, schema.and_def]
        obtain ⟨left, right⟩ := h
        cases hs with
        | inl h =>
          simp_all only [forall_const]
          sorry
        | inr h_1 =>
          simp_all only [forall_const]
          sorry
      | ex q q_ih =>
        simp_all [BoundedQuery.hasSubQuery.ex_hk q sq hs]

theorem BoundedQuery.isWellTyped.subQuery_def [folStruc] {n} {q : BoundedQuery n} {sq : BoundedQuery k} {hk : n ≤ k} (h : q.isWellTyped) :
  q.hasSubQuery hk sq → (sq.isWellTypedRec q.schema)
    := by
      simp_all [isWellTyped]
      intro h'
      have z := isWellTypedRec_sub (Finset.empty_subset q.schema) h
      have z' := BoundedQuery.isWellTypedRec.subQuery_def z h'
      have z'' := BoundedQuery.hasSubQuery.schema_def h'
      simp_all

theorem BoundedQuery.isWellTyped.schema_eq_attributesInQuery [folStruc] {n} {q : BoundedQuery n} (h : q.isWellTypedRec q.schema) :
  q.schema = q.attributesInQuery
    := by
      induction q
      all_goals aesop
