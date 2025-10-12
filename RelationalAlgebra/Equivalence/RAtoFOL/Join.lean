import RelationalAlgebra.Equivalence.RAtoFOL.Conversion
import RelationalAlgebra.FOL.RealizeProperties

variable {dbi q₁ q₂} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.j_def.mp (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁: ∀t, (ra_to_fol_query q₁ dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q₁)
  (ih₂: ∀t, (ra_to_fol_query q₂ dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q₂) :
    ∀t, (ra_to_fol_query (.j q₁ q₂) dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) := by
      intro t
      simp only [RA.Query.isWellTyped.j_def, ra_to_fol_query, FOL.Query.RealizeMin.def,
        FOL.BoundedQuery.schema.and_def, Finset.coe_union, RA.Query.evaluateT.j_def, joinT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq] at ⊢ h
      simp only [FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_and,
        FirstOrder.Language.BoundedFormula.realize_inf, and_imp]
      intro a_2 a_3 a_4
      have h_dom : t.Dom = ↑(q₁.schema dbi.schema) ∪ ↑(q₂.schema dbi.schema) := by
        rw [← ra_to_fol_query_schema h.1, ← ra_to_fol_query_schema h.2, a_4]

      have z' : ↑(ra_to_fol_query q₁ dbi.schema).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
      use t.restrict z'
      apply And.intro
      . apply ih₁
        . apply And.intro
          . rw [FOL.BoundedQuery.Realize.enlarge]
            exact a_2
            . simp [Set.subset_def, PFun.mem_dom]
            . rfl
            . rfl
          . simp_all only [FOL.Query.RealizeMin.def, and_imp]
            obtain ⟨left, right⟩ := h
            rfl

      . have z' : ↑(ra_to_fol_query q₂ dbi.schema).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
        use t.restrict z'
        apply And.intro
        . apply ih₂
          . apply And.intro
            . rw [FOL.BoundedQuery.Realize.enlarge]
              exact a_3
              . simp [Set.subset_def, PFun.mem_dom]
              . rfl
              . rfl
            . simp_all only [FOL.Query.RealizeMin.def, and_imp, Set.subset_union_left]
              obtain ⟨left, right⟩ := h
              rfl

        . intro a
          simp only [PFun.mem_restrict, Finset.mem_coe, and_imp, not_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only [Set.subset_union_right]
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only [Set.subset_union_left]
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          . intro h₁ h₂
            apply Part.eq_none_iff.mpr
            intro v
            by_cases c1 : (a ∈ q₁.schema dbi.schema)
            . simp_all only [FOL.Query.RealizeMin.def, ra_to_fol_query_schema, and_imp,
              forall_const, subset_refl, Set.subset_union_left, Set.subset_union_right, not_false_eq_true,
              implies_true]
            . by_cases c2 : (a ∈ q₂.schema dbi.schema)
              . simp_all only [FOL.Query.RealizeMin.def, ra_to_fol_query_schema, and_imp,
                forall_const, subset_refl, Set.subset_union_left, Set.subset_union_right, IsEmpty.forall_iff,
                implies_true, not_false_eq_true]
              . by_contra hc
                have z : ¬(a ∈ t.Dom) := by simp [h_dom, c1, c2]
                apply z
                apply Part.dom_iff_mem.mpr
                use v

theorem ra_to_fol_evalT.j_def.mpr (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁ : ∀t ∈ RA.Query.evaluateT dbi q₁, (ra_to_fol_query q₁ dbi.schema).RealizeMin dbi t)
  (ih₂ : ∀t ∈ RA.Query.evaluateT dbi q₂, (ra_to_fol_query q₂ dbi.schema).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) → (ra_to_fol_query (.j q₁ q₂) dbi.schema).RealizeMin dbi t := by
      intro t h_RA_eval
      have t_Dom : t.Dom = q₁.schema dbi.schema ∪ q₂.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema (.j q₁ q₂) h t h_RA_eval

      apply And.intro ?_
        (by simp_all [ra_to_fol_query_schema])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.j_def, RA.Query.evaluateT.j_def, joinT, PFun.mem_dom,
        forall_exists_index, Set.mem_union, not_or, not_exists, and_imp, Set.mem_setOf_eq,
        forall_const]
      simp_all only [FOL.Query.RealizeMin.def, ra_to_fol_query_schema]

      obtain ⟨left, right⟩ := h
      obtain ⟨w₁, h⟩ := h_RA_eval
      obtain ⟨hw₁, h⟩ := h
      obtain ⟨w₂, h⟩ := h
      obtain ⟨hw₂, right_1⟩ := h
      simp only [FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_and,
        FirstOrder.Language.BoundedFormula.realize_inf]
      apply And.intro
      · have w_Dom : w₁.Dom = q₁.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₁ left w₁ hw₁
        have z' : w₁.Dom ⊆ t.Dom := by simp_all
        simp_all only [Finset.coe_union, and_self, Set.subset_union_left, ← FOL.BoundedQuery.Realize.def]
        have z := (ih₁ w₁ hw₁)
        have ⟨h_sub, ht'⟩ : ∃h_sub : w₁.Dom ⊆ t.Dom, t.restrict h_sub = w₁ := by
          obtain ⟨l, r⟩ := z
          simp [*]; ext a v; simp [*]
          simp [Set.ext_iff] at r
          apply Iff.intro
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            have ⟨v', hv'⟩ := (r a).mpr left_1
            simp_all [← @Part.eq_some_iff]
          · intro a_1
            apply And.intro
            · simp only [← r a]
              use v
            · simp_all only [(right_1 a).1 v a_1]

        exact (FOL.BoundedQuery.Realize.enlarge h_sub ht' (by simp_all [ra_to_fol_query_schema])).mp z.1

      · have w_Dom : w₂.Dom = q₂.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₂ right w₂ hw₂
        have z' : w₂.Dom ⊆ t.Dom := by simp_all
        simp_all only [Finset.coe_union, and_self, Set.subset_union_left, ← FOL.BoundedQuery.Realize.def]
        have z := (ih₂ w₂ hw₂)
        have ⟨h_sub, ht'⟩ : ∃h_sub : w₂.Dom ⊆ t.Dom, t.restrict h_sub = w₂ := by
          obtain ⟨l, r⟩ := z
          simp [*]; ext a v; simp [*]
          simp [Set.ext_iff] at r
          apply Iff.intro
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            have ⟨v', hv'⟩ := (r a).mpr left_1
            simp_all [← @Part.eq_some_iff]
          · intro a_1
            apply And.intro
            · simp only [← r a]
              use v
            · simp_all only [(right_1 a).2.1 v a_1]

        exact (FOL.BoundedQuery.Realize.enlarge h_sub ht' (by simp_all [ra_to_fol_query_schema])).mp z.1

theorem ra_to_fol_evalT.j_def_eq (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁ : (ra_to_fol_query q₁ dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi q₁)
  (ih₂ : (ra_to_fol_query q₂ dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi q₂) :
    (ra_to_fol_query (.j q₁ q₂) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.j q₁ q₂) := by
      ext t
      apply Iff.intro
      . exact ra_to_fol_evalT.j_def.mp h
          (λ t' => ((Set.ext_iff.mp ih₁) t').mp)
          (λ t' => ((Set.ext_iff.mp ih₂) t').mp)
          t
      . exact ra_to_fol_evalT.j_def.mpr h
          (λ t' => ((Set.ext_iff.mp ih₁) t').mpr)
          (λ t' => ((Set.ext_iff.mp ih₂) t').mpr)
          t
