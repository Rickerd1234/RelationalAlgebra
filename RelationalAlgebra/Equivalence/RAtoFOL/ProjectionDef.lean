import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RelabelProperties

open RM


def projectAttribute (dropSet : RelationSchema) (a' : Attribute) : Attribute ⊕ Fin (dropSet.card) :=
  dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a')

theorem projectAttribute.def (dropSet : RelationSchema) (a' : Attribute) :
  projectAttribute dropSet a' = dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a') := rfl

@[simp]
theorem projectAttribute.empty_def :  projectAttribute ∅ = Sum.inl :=
  by unfold projectAttribute; simp

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
theorem projectQuery.def (folQ : FOL.Query) (rs : RelationSchema) : projectQuery folQ rs = (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs := rfl

@[simp]
theorem projectQuery.q_schema_def (folQ : FOL.Query) : projectQuery folQ folQ.schema = folQ := by simp; rw [Finset.sdiff_self]; simp

@[simp]
theorem projectQuery.schema_def (folQ : FOL.Query) (rs : RelationSchema) (h : rs ⊆ folQ.schema) : (projectQuery folQ rs).schema = rs := by
  ext a
  simp [projectQuery, FOL.BoundedQuery.relabel_schema]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, left, right⟩ := a_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only [projectAttribute_not_mem]
    . have z : w ∈ (folQ.schema \ rs) := by simp_all
      have z := projectAttribute_mem z
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    use a
    apply And.intro
    · exact h a_1
    · simp_all only [Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, projectAttribute_not_mem]

theorem projectQuery.not_sub_schema (folQ : FOL.Query) (rs : RelationSchema) : (projectQuery folQ (rs ∩ folQ.schema)) = (projectQuery folQ rs) := by
  simp_all
  have z : (folQ.schema \ (rs ∩ folQ.schema)) = folQ.schema \ rs := by simp
  rw [z]

@[simp]
theorem BoundedQuery.relabel_isWellTyped_projectAttribute {k} (dropSet : RelationSchema) (φ : FOL.BoundedQuery k) :
  (φ.relabel (projectAttribute dropSet)).isWellTyped dbs → φ.isWellTyped dbs := by
    induction φ with
    | _ => simp_all

theorem projectQuery.isWellTyped_def (folQ : FOL.Query) (rs : RelationSchema) (h' : (projectQuery folQ rs).isWellTyped dbs)
  : folQ.isWellTyped dbs := by
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

@[simp]
theorem projectQuery.Realize_empty_def [FOL.folStruc dbi] (folQ : FOL.Query) (rs : RelationSchema) (h : folQ.schema \ rs = ∅) (h' : rs ⊆ folQ.schema)
  : (projectQuery folQ rs).Realize dbi t xs = folQ.Realize dbi t xs := by
    have : rs = folQ.schema := by aesop
    simp_all
    rw [Finset.sdiff_self]
    simp_all

@[simp]
theorem default_comp {n m} {f : Fin m → Fin n} : ((default : Fin n →. Value) ∘ f) = (default : Fin m →. Value) := by
  ext i v
  simp_all only [Function.comp_apply]
  rfl
