import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RelabelProperties

open RM

variable {μ : Type}

def projectAttribute (dropSet : Finset String) (a' : String) : String ⊕ Fin (dropSet.card) :=
  dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a')

theorem projectAttribute.def (dropSet : Finset String) (a' : String) :
  projectAttribute dropSet a' = dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a') := rfl

@[simp]
theorem projectAttribute.empty_def : projectAttribute (∅ : Finset String) = Sum.inl :=
  by unfold projectAttribute; simp

@[simp]
theorem projectAttribute_eq {x y : String} : projectAttribute dropSet x = Sum.inl y → x = y := by
    simp [projectAttribute.def]
    intro a
    split at a
    next h => simp_all only [reduceCtorEq]
    next h => simp_all only [Sum.inl.injEq]

@[simp]
theorem projectAttribute_not_mem {a' : String} (h : a' ∉ dropSet) : projectAttribute dropSet a' = Sum.inl a' := by
    rw [projectAttribute.def]
    exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h

@[simp]
theorem projectAttribute_mem {a' : String} (h : a' ∈ dropSet) :
  ∃x, projectAttribute dropSet a' = Sum.inr x := by
    rw [projectAttribute.def]
    simp_all only [↓reduceDIte, Sum.inr.injEq, exists_eq']

def projectQuery (folQ : FOL.Query dbs) (rs : Finset String) : FOL.Query dbs :=
  (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs

@[simp]
theorem projectAttribute.Injective {dropSet : Finset String} : (projectAttribute dropSet).Injective := by
    rw [Function.Injective]
    unfold projectAttribute
    intro a₁ a₂
    rw [@dite_eq_iff']
    split
    all_goals (
      rename_i h
      intro ⟨l, r⟩
    )
    . by_cases hc : a₁ ∈ dropSet
      . exact (RelationSchema.index_inj hc h).mp (Sum.inr.inj_iff.mp (l hc))
      . exact False.elim (Sum.inl_ne_inr (r hc))
    . by_cases hc : a₁ ∈ dropSet
      . exact False.elim (Sum.inr_ne_inl (l hc))
      . exact Sum.inl.inj_iff.mp (r hc)

@[simp]
theorem projectQuery.def (folQ : FOL.Query dbs) (rs : Finset String) : projectQuery folQ rs = (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs := rfl

@[simp]
theorem projectQuery.q_schema_def (folQ : FOL.Query dbs) : projectQuery folQ folQ.schema = folQ := by
  rw [projectQuery.def, Finset.sdiff_self, projectAttribute.empty_def, FOL.BoundedQuery.relabel_Sum_inl folQ rfl, FOL.castLE_rfl];
  . simp
  . simp

@[simp]
theorem projectQuery.schema_def (folQ : FOL.Query dbs) (rs : Finset String) (h : rs ⊆ folQ.schema) : (projectQuery folQ rs).schema = rs := by
  ext a
  simp [projectQuery, FOL.BoundedQuery.relabel_schema]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, left, right⟩ := a_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only
    . have z : w ∈ (folQ.schema \ rs) := by simp_all
      have z := projectAttribute_mem z
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    use a
    apply And.intro
    · exact h a_1
    · simp_all only [Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, projectAttribute_not_mem]

theorem projectQuery.not_sub_schema (folQ : FOL.Query dbs) (rs : Finset String) : (projectQuery folQ (rs ∩ folQ.schema)) = (projectQuery folQ rs) := by
  simp_all
  have z : (folQ.schema \ (rs ∩ folQ.schema)) = folQ.schema \ rs := by simp
  rw [z]

@[simp]
theorem projectQuery.Realize_empty_def [FOL.folStruc dbi] (folQ : FOL.Query dbi.schema) (rs : Finset String) (h : folQ.schema \ rs = ∅) (h' : rs ⊆ folQ.schema)
  : (projectQuery folQ rs).Realize dbi t xs = folQ.Realize dbi t xs := by
    have : rs = folQ.schema := by aesop
    simp_all
    rw [Finset.sdiff_self]
    simp_all

@[simp]
theorem default_comp {n m} {f : Fin m → Fin n} : ((default : Fin n →. μ) ∘ f) = (default : Fin m →. μ) := by
  ext i v
  simp_all only [Function.comp_apply]
  rfl
