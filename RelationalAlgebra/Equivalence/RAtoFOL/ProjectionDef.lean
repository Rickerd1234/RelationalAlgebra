import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.Properties

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

@[simp]
theorem projectQuery.Realize_restrict_def [FOL.folStruc dbi] (folQ : FOL.Query) (rs : RelationSchema) (h : ↑rs ⊆ t.Dom) (h' : folQ.isWellTyped dbi.schema)
  : folQ.RealizeDom dbi t → (projectQuery folQ rs).Realize dbi (t.restrict h) default := by
    intro a
    simp_all only [«def», Nat.add_zero, FOL.BoundedQuery.Realize.exs_def, FOL.BoundedQuery.Realize.relabel_def,
      Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq]
    have hs : ↑folQ.schema = t.Dom := by
      exact Eq.symm (FOL.realize_query_dom dbi a)
    unfold projectAttribute
    cases folQ with
    | R dbs rn tMap =>
      use λ i => t (RelationSchema.fromIndex i)

      simp at a
      simp_all only [FOL.BoundedQuery.isWellTyped.R_def, FOL.Query.RealizeDom.def, Nat.add_zero,
        FOL.BoundedQuery.relabel.R_def, FOL.BoundedQuery.Realize.R_def, FOL.Term.realizeSome.def,
        FOL.BoundedQuery.toFormula_rel, FirstOrder.Language.BoundedFormula.realize_rel,
        FOL.BoundedQuery.schema.R_def, Set.coe_toFinset, Finset.mem_sdiff, Set.mem_toFinset,
        PFun.mem_dom, subset_refl, and_true, implies_true, and_self]
      subst h'
      simp_all only [FOL.folStruc_apply_RelMap, FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
        PFun.mem_dom]
      obtain ⟨left, right⟩ := a
      apply And.intro
      · intro i
        have ⟨t', ht'⟩ := FOL.Term.cases (tMap i)
        simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
          FirstOrder.Language.Term.realize_var]
        cases t' with
        | inl
          val =>
          simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
            Sum.elim_inl, Function.comp_apply]
          split
          next h_1 =>
            simp_all only [Part.dom_iff_mem, Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            have := left i
            simp [ht'] at this
            exact this
          next
            h_1 =>
            simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
              PFun.mem_dom, not_and, Decidable.not_not, forall_exists_index, Sum.elim_inl,
              PFun.restrict, Part.restrict, Finset.mem_coe]
            have := left i
            simp [ht', Part.dom_iff_mem] at this
            obtain ⟨z, hz⟩ := this
            exact h_1 z hz
        | inr
          val_1 =>
          simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
            Sum.elim_inr, Function.comp_apply]
          exact Fin.elim0 val_1

      · apply Set.mem_of_eq_of_mem ?_ right
        ext a v
        unfold FOL.ArityToTuple
        simp_all only [Pi.default_def, FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
          PFun.mem_dom]
        apply Iff.intro
        · intro a_1
          split
          next
            h_1 =>
            simp_all only [↓reduceDIte, FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
              PFun.mem_dom]
            have ⟨z, hz⟩ := FOL.Term.cases (tMap (RelationSchema.index h_1))
            simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
              FirstOrder.Language.Term.realize_var]
            cases z with
            | inl
              val =>
              simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
                Sum.elim_inl, Function.comp_apply]
              split at a_1
              next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
              next h_2 =>
                simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
                  not_and, Decidable.not_not, forall_exists_index, Sum.elim_inl, PFun.mem_restrict,
                  Finset.mem_coe]
            | inr
              val_1 =>
              simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom,
                Sum.elim_inr, Function.comp_apply]
              exact Fin.elim0 val_1
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]
        . intro a_1
          split
          next
            h_1 =>
            have ⟨z, hz⟩ := FOL.Term.cases (tMap (RelationSchema.index h_1))
            simp_all only [↓reduceDIte, FirstOrder.Language.Term.realize_var, FOL.BoundedQuery.schema.R_def,
              Finset.mem_sdiff, Set.mem_toFinset, PFun.mem_dom]
            cases z with
            | inl
              val =>
              simp_all only [Sum.elim_inl, FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
                PFun.mem_dom, Function.comp_apply]
              split
              next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
              next
                h_2 =>
                simp_all only [FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
                  PFun.mem_dom, not_and, Decidable.not_not, forall_exists_index, Sum.elim_inl,
                  PFun.mem_restrict, Finset.mem_coe, and_true]
                apply h_2 v a_1
            | inr
              val_1 =>
              simp_all only [Sum.elim_inr, FOL.BoundedQuery.schema.R_def, Finset.mem_sdiff, Set.mem_toFinset,
                PFun.mem_dom, Function.comp_apply]
              exact Fin.elim0 val_1
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]

    | and =>
      simp at a
      simp_all
      obtain ⟨left, right⟩ := h'
      obtain ⟨left_1, right_1⟩ := a

      use (λ i => t (RelationSchema.fromIndex i))

      apply And.intro
      all_goals (
        try apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp left_1
        try apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp right_1
        . ext a v
          exact Fin.elim0 a
        . ext a v
          simp_all only [Function.comp_apply]
          apply Iff.intro
          · intro a_1
            split
            next h_1 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            next
              h_1 =>
              simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, and_true]
              simp [Set.ext_iff, PFun.mem_dom] at hs
              apply h_1
              simp_all only [forall_exists_index]
              apply Exists.intro v a_1
          · intro a_1
            split at a_1
            next h_1 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            next h_1 => simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe]
      )

    | tEq q t₁ t₂ =>
      simp at a
      simp_all only [FOL.BoundedQuery.isWellTyped.tEq_def, FOL.BoundedQuery.schema.tEq_def,
        subset_refl, and_true, Finset.mem_sdiff, and_self, FOL.BoundedQuery.Realize.tEq_def,
        FOL.Term.realizeSome.def]
      obtain ⟨left, right⟩ := h'
      obtain ⟨left_1, right_1⟩ := a
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right_1⟩ := right_1
      obtain ⟨left_4, right_1⟩ := right_1

      use (λ i => t (RelationSchema.fromIndex i))

      apply And.intro
      · try apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp left_1
        . ext a v
          exact Fin.elim0 a
        . ext a v
          simp_all only [Function.comp_apply]
          apply Iff.intro
          · intro a_1
            split
            next h_1 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            next
              h_1 =>
              simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, and_true]
              apply h_1
              simp [Set.ext_iff] at hs
              simp_all only [forall_exists_index]
              apply Exists.intro v a_1
          · intro a_1
            split at a_1
            next h_1 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            next h_1 => simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe]
      · apply And.intro
        · rw [Part.dom_iff_mem] at *
          obtain ⟨y, hy⟩ := left_3
          use y
          have ⟨t', ht'⟩ := FOL.Term.cases t₁
          subst ht'
          simp_all only [FirstOrder.Language.Term.realize_var]
          cases t' with
          | inl val =>
            simp_all
            split
            next left_2_1 h_2 =>
              simp_all only [FOL.BoundedQuery.hasSafeTerm_mem_schema, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe,
                and_self]
            next left_2_1 h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
          | inr val_1 =>
            simp_all only [Sum.elim_inr, Function.comp_apply]
            exact Fin.elim0 val_1
        · apply And.intro
          · rw [Part.dom_iff_mem] at *
            obtain ⟨y, hy⟩ := left_4
            use y
            have ⟨t', ht'⟩ := FOL.Term.cases t₂
            subst ht'
            simp_all only [FirstOrder.Language.Term.realize_var]
            obtain ⟨w, h_1⟩ := left_3
            cases t' with
            | inl val =>
              simp_all
              split
              next left_2_1 h_2 =>
                simp_all only [FOL.BoundedQuery.hasSafeTerm_mem_schema, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe,
                  and_self]
              next left_2_1 h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
            | inr val_1 =>
              simp_all only [Sum.elim_inr, Function.comp_apply]
              exact Fin.elim0 val_1
          · have ⟨t₁', ht₁'⟩ := FOL.Term.cases t₁
            have ⟨t₂', ht₂'⟩ := FOL.Term.cases t₂
            subst ht₁' ht₂'
            simp_all only [FirstOrder.Language.Term.realize_var]
            cases t₁' with
            | inl val =>
              cases t₂' with
              | inl val_1 =>
                simp [FirstOrder.Language.BoundedFormula.Realize] at right_1
                simp_all only [FOL.BoundedQuery.hasSafeTerm_mem_schema, Sum.elim_inl]
                ext v
                simp_all only [FirstOrder.Language.Term.realize_var, Sum.elim_inl, Function.comp_apply, true_and,
                  dite_not]
                apply Iff.intro
                · intro a
                  split
                  next h_1 =>
                    simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    split at a
                    next h_2 => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
                  next h_1 =>
                    simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
                    split at a
                    next h_2 => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
                · intro a
                  split
                  next h_1 =>
                    simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    split at a
                    next h_2 => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
                  next h_1 =>
                    simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
                    split at a
                    next h_2 => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, true_and]
                    next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
              | inr
                val_2 =>
                simp_all only [FOL.BoundedQuery.hasSafeTerm_mem_schema, Sum.elim_inl, Sum.elim_inr]
                exact Fin.elim0 val_2
            | inr val_1 =>
              exact Fin.elim0 val_1

    | ex =>
      simp at a
      simp_all
      obtain ⟨w, h_1⟩ := a

      use (λ i => t (RelationSchema.fromIndex i))
      use w

      try apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp h_1
      . rfl
      . ext a v
        simp_all only [Function.comp_apply]
        apply Iff.intro
        · intro a_1
          split
          next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
          next
            h_2 =>
            simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe, and_true]
            apply h_2
            simp [Set.ext_iff] at hs
            simp_all only [forall_exists_index]
            apply Exists.intro v a_1

        · intro a_1
          split at a_1
          next h_2 => simp_all only [Sum.elim_inr, RelationSchema.fromIndex_index_eq]
          next h_2 => simp_all only [not_and, Decidable.not_not, Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe]
