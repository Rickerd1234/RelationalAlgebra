import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RelabelProperties

/- Helper functions and definitions for Projection, most complex case on this conversion. -/

open RM

variable {ρ α μ : Type} [LinearOrder α]

/-- Relabel function for an attribute using the 'drop set' (`folQ.schema \ rs : Finset α` containing the variables to be dropped).
  Relabel the free FOL variables consistently:
  - Projected variable (`x ∈ rs`) → `x`.
  - Dropped variable (`x ∉ rs`, so `h : x ∈ dropSet`) → `RelationSchema.index h`.
-/
def projectAttribute (dropSet : Finset α) (a' : α) : α ⊕ Fin (dropSet.card) :=
  dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a')

theorem projectAttribute.def (dropSet : Finset α) (a' : α) :
  projectAttribute dropSet a' = dite (a' ∈ dropSet) (λ h' => Sum.inr (RelationSchema.index h')) (λ _ => Sum.inl a') := rfl

@[simp]
theorem projectAttribute.empty_def : projectAttribute (∅ : Finset α) = Sum.inl :=
  by unfold projectAttribute; simp only [Finset.card_empty, Finset.notMem_empty, ↓reduceDIte]

theorem projectAttribute_eq {x y : α} : projectAttribute dropSet x = Sum.inl y → x = y := by
    simp [projectAttribute.def]
    intro a
    split at a
    next h => simp_all only [reduceCtorEq]
    next h => simp_all only [Sum.inl.injEq]

@[simp]
theorem projectAttribute_not_mem {a' : α} (h : a' ∉ dropSet) : projectAttribute dropSet a' = Sum.inl a' := by
    rw [projectAttribute.def]
    exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h

@[simp]
theorem projectAttribute_mem {a' : α} (h : a' ∈ dropSet) :
  ∃x, projectAttribute dropSet a' = Sum.inr x := by
    rw [projectAttribute.def]
    simp_all only [↓reduceDIte, Sum.inr.injEq, exists_eq']

/-- Project an entire query using a 'drop set' (`folQ.schema \ rs : Finset α` containing the variables to be dropped).
  1. Relabel the free FOL variables consistently:
  - Projected variable (`x ∈ rs`) → `x`.
  - Dropped variable (`x ∉ rs`, so `h : x ∈ dropSet`) → `RelationSchema.index h`.
  2. Bind all fresh bound (`Fin n`) variables to an existential quantifier.
-/
def projectQuery {dbs : ρ → Finset α} (folQ : FOL.Query dbs) (rs : Finset α) : FOL.Query dbs :=
  (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs

@[simp]
theorem projectAttribute.Injective {dropSet : Finset α} : (projectAttribute dropSet).Injective := by
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
theorem projectQuery.def (folQ : FOL.Query dbs) (rs : Finset α) : projectQuery folQ rs = (folQ.relabel (projectAttribute (folQ.schema \ rs))).exs := rfl

@[simp]
theorem projectQuery.q_schema_def {dbs : ρ → Finset α} (folQ : FOL.Query dbs) : projectQuery folQ folQ.schema = folQ := by
  rw [projectQuery.def, Finset.sdiff_self, projectAttribute.empty_def, FOL.BoundedQuery.relabel_Sum_inl folQ rfl, FOL.castLE_rfl];
  . simp only [Finset.card_empty, Nat.add_zero, FOL.BoundedQuery.exs.eq_1]
  . simp only [add_zero, le_refl]

/-- `projectQuery` results to the right schema (`rs`), given that `rs ⊆ folQ.schema`-/
@[simp]
theorem projectQuery.schema_def {dbs : ρ → Finset α} (folQ : FOL.Query dbs) (rs : Finset α) (h : rs ⊆ folQ.schema) : (projectQuery folQ rs).schema = rs := by
  ext a
  simp only [projectQuery, Nat.add_zero, FOL.BoundedQuery.schema.exs_def,
    FOL.BoundedQuery.relabel_schema, Finset.mem_pimage, Part.mem_ofOption, Option.mem_def,
    Sum.getLeft?_eq_some_iff]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, left, right⟩ := a_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only
    . have z : w ∈ (folQ.schema \ rs) := Finset.mem_sdiff.mpr ⟨left, h⟩
      have z := projectAttribute_mem z
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    use a
    apply And.intro
    · exact h a_1
    · simp_all only [Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, projectAttribute_not_mem]

theorem projectQuery.not_sub_schema (folQ : FOL.Query dbs) (rs : Finset α) : (projectQuery folQ (rs ∩ folQ.schema)) = (projectQuery folQ rs) := by
  rw [@«def»]
  rw [Finset.sdiff_inter_self_right]
  rw [← @«def»]

@[simp]
theorem projectQuery.Realize_empty_def [FOL.folStruc dbi] (folQ : FOL.Query dbi.schema) (rs : Finset α) (h : folQ.schema \ rs = ∅) (h' : rs ⊆ folQ.schema)
  : (projectQuery folQ rs).Realize dbi t xs = folQ.Realize dbi t xs := by
    have : rs = folQ.schema := Finset.Subset.antisymm h' (Finset.sdiff_eq_empty_iff_subset.mp h)
    subst this
    rw [«def»]
    rw [sdiff_self]
    rw [@Finset.bot_eq_empty]
    rw [@projectAttribute.empty_def]
    simp only [Finset.card_empty, Nat.add_zero, add_zero, le_refl, FOL.BoundedQuery.relabel_Sum_inl,
      FOL.castLE_rfl, FOL.BoundedQuery.exs.eq_1]

@[simp]
theorem default_comp {n m} {f : Fin m → Fin n} : ((default : Fin n →. μ) ∘ f) = (default : Fin m →. μ) := by
  ext i v
  simp_all only [Function.comp_apply]
  rfl
