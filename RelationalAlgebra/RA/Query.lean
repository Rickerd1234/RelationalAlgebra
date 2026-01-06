import RelationalAlgebra.RA.RelationalAlgebra

open RM

namespace RA

/-- Type definition for Relational Algebra Queries -/
inductive Query (ρ α : Type) : Type
  | R: ρ → Query ρ α
  | s: α → α → Query ρ α → Query ρ α
  | p: Finset α → Query ρ α → Query ρ α
  | j: Query ρ α → Query ρ α → Query ρ α
  | r: (α → α) → Query ρ α → Query ρ α
  | u: Query ρ α → Query ρ α → Query ρ α
  | d: Query ρ α → Query ρ α → Query ρ α


/-- Recursive schema definition -/
@[simp]
def Query.schema [DecidableEq α] : (q : Query ρ α) → (dbs : ρ → Finset α) → Finset α
  | .R rn => λ dbs => dbs rn
  | .s _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j sq1 sq2 => λ dbs => sq1.schema dbs ∪ sq2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  | .u sq1 _ => sq1.schema
  | .d sq1 _ => sq1.schema


/-- Recursive well-typed property -/
@[simp]
def Query.isWellTyped [DecidableEq α] (dbs : ρ → Finset α) (q : Query ρ α) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j sq₁ sq₂ => sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Bijective
  | .u sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs
  | .d sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs


/-- Recursive tuple evaluation -/
@[simp]
def Query.evaluateT (dbi : DatabaseInstance ρ α μ) (q : Query ρ α) : Set (α →. μ) :=
  match q with
  | .R rn => (dbi.relations rn).tuples
  | .s a b sq => selectionT (sq.evaluateT dbi) a b
  | .p rs sq => projectionT (sq.evaluateT dbi) rs
  | .j sq₁ sq₂ => joinT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi)
  | .r f sq => renameT (sq.evaluateT dbi) f
  | .u sq1 sq2 => unionT (sq1.evaluateT dbi) (sq2.evaluateT dbi)
  | .d sq1 sq2 => diffT (sq1.evaluateT dbi) (sq2.evaluateT dbi)

/-- Proof that each well-typed query will result in tuples with the correct schema -/
theorem Query.evaluate.validSchema [DecidableEq α] (q : Query ρ α) (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → PFun.Dom t = ↑(q.schema dbi.schema) := by
  induction q with
  | R rn =>
    intro t h_t
    simp_all only [isWellTyped, evaluateT, schema, ← DatabaseInstance.validSchema]
    exact (dbi.relations rn).validSchema t h_t
  | s a b sq ih =>
    simp_all only [isWellTyped, evaluateT, selectionT, schema]
    simp_all only [forall_const, Set.mem_setOf_eq, implies_true]
  | p rs sq ih =>
    intro t h_t
    simp_all [isWellTyped, evaluateT, projectionT, schema]
    apply projectionDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ ?_ h.2
    . simp_all only [projectionT, Set.mem_setOf_eq]
  | j sq1 sq2 ih1 ih2 =>
    intro t h_t
    simp_all only [isWellTyped, forall_const]
    apply joinDom
      ⟨sq1.schema dbi.schema, evaluateT dbi sq1, ih1⟩
      ⟨sq2.schema dbi.schema, evaluateT dbi sq2, ih2⟩
      h_t
  | r f sq ih =>
    intro t h_t
    apply renameDom ⟨sq.schema dbi.schema, evaluateT dbi sq, (by simp_all)⟩ h.2
    simp_all only [evaluateT, renameT, Set.mem_setOf_eq]
  | u sq1 sq2 ih =>
    intro _ ht
    simp [isWellTyped, evaluateT, unionT, schema] at *
    cases ht
    all_goals simp_all only
  | d sq1 sq2 ih =>
    intro _ ht
    simp [isWellTyped, evaluateT, diffT, schema] at *
    cases ht
    all_goals simp_all only

/-- Query evaluation for `RelationInstance` -/
def Query.evaluate [DecidableEq α] (dbi : DatabaseInstance ρ α μ) (q : Query ρ α) (h : q.isWellTyped dbi.schema) : RelationInstance α μ :=
  ⟨
    q.schema dbi.schema,
    q.evaluateT dbi,
    by exact fun t a ↦ evaluate.validSchema q h t a
  ⟩


/- Some helper theorems -/
@[simp]
theorem PFun.restrict.def_eq {α β} {t : α →. β} {s : Set α} (h : s ⊆ t.Dom) (h' : s = t.Dom) :
  t.restrict h = t := by
    ext a b; aesop

@[simp]
theorem Query.evaluateT.mem_restrict [DecidableEq α] {q : Query ρ α} (z : ↑(q.schema dbi.schema) ⊆ t.Dom)
  (h : q.isWellTyped dbi.schema) (h' : t ∈ q.evaluateT dbi) :
    t.restrict z ∈ q.evaluateT dbi := by
      have z' := (q.evaluate dbi h).validSchema t h'; have z'' := PFun.restrict.def_eq z z'.symm; simp_all only

/-- Proof that the range, for all tuples in a well-typed Query evaluation, is a subset of the database domain -/
theorem Query.evaluateT.dbi_domain [DecidableEq α] [Nonempty α] {dbi : DatabaseInstance ρ α μ} {q : Query ρ α} (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → t.ran ⊆ dbi.domain
  := by
    induction q with
    | R rn =>
      intro t ht
      simp_all [PFun.ran, DatabaseInstance.domain]
      intro v a hv
      use rn, a, t, ht
      exact Part.eq_some_iff.mpr hv

    | s a b sq => simp_all only [isWellTyped, evaluateT, selectionT, Set.mem_setOf_eq, implies_true]

    | p rs sq ih =>
      simp_all [projectionT]
      intro t' t ht ha
      have z' : PFun.ran t' ⊆ PFun.ran t := by
        simp only [PFun.ran, Set.setOf_subset_setOf, forall_exists_index]
        intro v a h_dom
        by_cases hc : a ∈ rs
        . simp_all only; exact Exists.intro a h_dom
        . simp_all only [not_false_eq_true, Part.notMem_none]
      exact Set.Subset.trans z' (ih t ht)

    | j q₁ q₂ ih₁ ih₂ =>
      simp_all only [isWellTyped, evaluateT, joinT, joinSingleT, PFun.mem_dom, forall_exists_index,
        Set.mem_union, not_or, not_exists, and_imp, Set.mem_setOf_eq, forall_const]
      intro t' t₁ ht₁ t₂ ht₂ ht'

      have z' : PFun.ran t' ⊆ (PFun.ran t₁) ∪ (PFun.ran t₂) := by
        simp only [PFun.ran, Set.setOf_subset_setOf, Set.union_def]
        intro v ⟨a, ha⟩
        by_cases hc₁ : a ∈ t₁.Dom
        . simp_all; have ⟨y, hy⟩ := hc₁; rw [(ht' a).1 y hy] at ha; apply Or.inl (Exists.intro a ha)
        . by_cases hc₂ : a ∈ t₂.Dom
          . simp_all; have ⟨y, hy⟩ := hc₂; rw [(ht' a).2.1 y hy] at ha; apply Or.inr (Exists.intro a ha)
          . simp_all only [PFun.mem_dom, not_exists, Set.mem_setOf_eq, not_false_eq_true, implies_true,
              Part.notMem_none]

      have : t₁.ran ∪ t₂.ran ⊆ dbi.domain := by simp_all only [Set.union_subset_iff, and_self]
      exact fun ⦃a⦄ a_1 ↦ this (z' a_1)

    | r f sq ih =>
      simp_all only [isWellTyped, evaluateT, renameT, Set.mem_setOf_eq,
        forall_const]
      intro t ht

      have z := ih (t ∘ f) ht
      have z' : (PFun.ran t) ⊆ PFun.ran (t ∘ f) := by
        simp [PFun.ran]
        intro v a ha
        use (f.invFun a)
        simp_all only [f_inv_id]

      exact fun ⦃a⦄ a_1 ↦ z (z' a_1)

    | u q₁ q₂ ih₁ ih₂ =>
      simp_all only [isWellTyped, evaluateT, unionT, Set.mem_union, forall_const]
      intro t ht
      cases ht with
      | inl ht₁ => exact ih₁ t ht₁
      | inr ht₂ => exact ih₂ t ht₂

    | d q nq ih nih =>
      simp_all only [isWellTyped, evaluateT, diffT, Set.mem_diff, implies_true]
