import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.Properties

open RM


def projectAttribute (dropSet : RelationSchema) (a' : Attribute) : Attribute ⊕ Fin (dropSet.card) :=
  dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a')

theorem projectAttribute.def (dropSet : RelationSchema) (a' : Attribute) :
  projectAttribute dropSet a' = dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a') := rfl

@[simp]
theorem projectAttribute_eq {dropSet x y} : projectAttribute dropSet x = Sum.inl y → x = y := by
    simp [projectAttribute.def]
    intro a
    split at a
    next h => simp_all only [reduceCtorEq]
    next h => simp_all only [not_and, Decidable.not_not, Sum.inl.injEq]

@[simp]
theorem projectAttribute_not_mem {dropSet a'} (h : a' ∉ dropSet) : projectAttribute dropSet a' = Sum.inl a' := by
    simp [projectAttribute.def]
    exact h

@[simp]
theorem projectAttribute_mem {dropSet a'} (h : a' ∈ dropSet) :
  ∃x, projectAttribute dropSet a' = Sum.inr x := by
    simp [projectAttribute.def]
    simp_all only [not_false_eq_true, and_self, ↓reduceDIte, Sum.inr.injEq, exists_eq']

def projectQuery (folQ : FOL.Query) (rs : RelationSchema) : FOL.Query :=
  (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs

@[simp]
theorem projectAttribute.Injective : (projectAttribute dropSet).Injective :=
  by simp [Function.Injective, projectAttribute]; aesop

@[simp]
theorem projectQuery.def [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) : projectQuery folQ rs = (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs := rfl

@[simp]
theorem projectQuery.schema_def [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) (h : rs ⊆ folQ.schema) : (projectQuery folQ rs).schema = rs := by
  ext a
  apply Iff.intro
  · intro a_1
    simp [projectQuery] at a_1
    obtain ⟨w, h_1⟩ := a_1
    obtain ⟨left, right⟩ := h_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only [projectAttribute_not_mem]
    . have z : w ∈ (folQ.schema \ rs) := by simp_all
      have z := projectAttribute_mem z
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    simp_all [projectQuery]
    use a
    apply And.intro
    · exact h a_1
    · simp_all only [Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, projectAttribute_not_mem]

theorem projectQuery.not_sub_schema [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) : (projectQuery folQ (rs ∩ folQ.schema)) = (projectQuery folQ rs) := by
  simp_all
  have z : (folQ.schema \ (rs ∩ folQ.schema)) = folQ.schema \ rs := by simp
  rw [z]

@[simp]
theorem BoundedQuery.relabel_isWellTyped_projectAttribute [FOL.folStruc] {k} (dropSet : RelationSchema) (φ : FOL.BoundedQuery k) :
  (φ.relabel (projectAttribute dropSet)).isWellTyped → φ.isWellTyped := by
    induction φ with
    | _ => simp_all

theorem projectQuery.isWellTyped_def [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) (h' : (projectQuery folQ rs).isWellTyped)
  : folQ.isWellTyped := by
    cases folQ with

    | R _ _ _ => simp_all

    | tEq q t₁ t₂ =>
      simp_all only [projectQuery, FOL.BoundedQuery.isWellTyped.exs_def]
      exact
        BoundedQuery.relabel_isWellTyped_projectAttribute ((q.tEq t₁ t₂).schema \ rs)
          (q.tEq t₁ t₂) h'

    | and q₁ q₂ =>
      simp_all only [projectQuery, FOL.BoundedQuery.isWellTyped.exs_def, FOL.BoundedQuery.isWellTyped.and_def]
      exact BoundedQuery.relabel_isWellTyped_projectAttribute ((q₁.and q₂).schema \ rs) (q₁.and q₂) h'

    | ex q =>
      simp_all only [projectQuery, FOL.BoundedQuery.relabel.ex_def, FOL.BoundedQuery.isWellTyped.exs_def]
      exact BoundedQuery.relabel_isWellTyped_projectAttribute (q.ex.schema \ rs) q h'
