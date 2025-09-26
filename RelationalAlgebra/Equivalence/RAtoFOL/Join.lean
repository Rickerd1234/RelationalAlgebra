import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi q₁ q₂} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.j_def.mp (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁: ∀t, (ra_to_fol_query q₁ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q₁)
  (ih₂: ∀t, (ra_to_fol_query q₂ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q₂) :
    ∀t, (ra_to_fol_query (.j q₁ q₂) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) := by
      intro t
      simp only [RA.Query.isWellTyped.j_def, ra_to_fol_query, FOL.Query.RealizeDom.def,
        FOL.BoundedQuery.schema.and_def, Finset.coe_union, RA.Query.evaluateT.j_def, joinT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq] at ⊢ h
      simp only [FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_and,
        FirstOrder.Language.BoundedFormula.realize_inf, and_imp]
      intro a_2 a_3 a_4
      have h_dom : t.Dom = ↑(q₁.schema dbi.schema) ∪ ↑(q₂.schema dbi.schema) := by
        obtain ⟨left, right⟩ := h

        have z₁ := FOL.BoundedQuery.Realize.schema_sub_Dom (ra_to_fol_query.isWellTyped q₁ dbi.schema left) a_2
        have z₂ := FOL.BoundedQuery.Realize.schema_sub_Dom (ra_to_fol_query.isWellTyped q₂ dbi.schema right) a_3
        simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
          forall_const]

        apply Set.Subset.antisymm a_4 (Set.union_subset z₁ z₂)

      have z' : ↑(ra_to_fol_query q₁ dbi.schema).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
      use t.restrict (z')
      apply And.intro
      . apply ih₁
        . apply And.intro
          . exact FOL.BoundedQuery.Realize.tuple_restrict2 (by simp [h.1]) z' a_2
          . simp_all
            simp [PFun.Dom, Part.dom_iff_mem, z', Set.subset_def]
            intro x a x_1 h_1
            simp_all only [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, Set.subset_union_left]

      . have z' : ↑(ra_to_fol_query q₂ dbi.schema).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
        use t.restrict (z')
        apply And.intro
        . apply ih₂
          . apply And.intro
            . exact FOL.BoundedQuery.Realize.tuple_restrict2 (by simp [h.2]) z' a_3
            . simp_all
              simp [PFun.Dom, Part.dom_iff_mem, z', Set.subset_def]
              intro x a x_1 h_1
              simp_all only [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, Set.subset_union_left]

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
            . simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
              forall_const, subset_refl, Set.subset_union_left, Set.subset_union_right, not_false_eq_true,
              implies_true]
            . by_cases c2 : (a ∈ q₂.schema dbi.schema)
              . simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
                forall_const, subset_refl, Set.subset_union_left, Set.subset_union_right, IsEmpty.forall_iff,
                implies_true, not_false_eq_true]
              . by_contra hc
                have z : ¬(a ∈ t.Dom) := by simp [h_dom, c1, c2]
                apply z
                apply Part.dom_iff_mem.mpr
                use v

theorem ra_to_fol_evalT.j_def.mpr (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁ : ∀t ∈ RA.Query.evaluateT dbi q₁, (ra_to_fol_query q₁ dbi.schema).RealizeDom dbi t)
  (ih₂ : ∀t ∈ RA.Query.evaluateT dbi q₂, (ra_to_fol_query q₂ dbi.schema).RealizeDom dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) → (ra_to_fol_query (.j q₁ q₂) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      have t_Dom : t.Dom = q₁.schema dbi.schema ∪ q₂.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema (.j q₁ q₂) h t h_RA_eval

      apply And.intro ?_
        (by simp_all [ra_to_fol_query_schema])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.j_def, RA.Query.evaluateT.j_def, joinT, PFun.mem_dom,
        forall_exists_index, Set.mem_union, not_or, not_exists, and_imp, Set.mem_setOf_eq,
        forall_const]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]

      obtain ⟨left, right⟩ := h
      obtain ⟨w₁, h⟩ := h_RA_eval
      obtain ⟨hw₁, h⟩ := h
      obtain ⟨w₂, h⟩ := h
      obtain ⟨hw₂, right_1⟩ := h
      simp only [FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_and,
        FirstOrder.Language.BoundedFormula.realize_inf]
      apply And.intro
      · have z := (ih₁ w₁ hw₁)
        have w_Dom : w₁.Dom = q₁.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₁ left w₁ hw₁
        have z' : w₁.Dom ⊆ t.Dom := by simp_all
        apply FOL.BoundedQuery.Realize.tuple_restrict (ra_to_fol_query.isWellTyped q₁ dbi.schema left) z.1 z'

        ext a v
        simp [PFun.mem_restrict]
        by_cases hc : a ∈ w₁.Dom
        . simp [PFun.mem_dom] at hc
          have ⟨y, hy⟩ := hc
          have z'' := (right_1 a).1 y hy
          simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, true_and]
        . simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, Finset.mem_coe]
          simp [← Finset.mem_coe, (Set.ext_iff.mp w_Dom.symm) a] at hc
          apply Iff.intro
          · intro a_1
            exact False.elim (hc v a_1)
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            exact False.elim (hc w h)


      · have z := (ih₂ w₂ hw₂)
        have w_Dom : w₂.Dom = q₂.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₂ right w₂ hw₂
        have z' : w₂.Dom ⊆ t.Dom := by simp_all
        apply FOL.BoundedQuery.Realize.tuple_restrict (ra_to_fol_query.isWellTyped q₂ dbi.schema right) z.1 z'

        ext a v
        simp [PFun.mem_restrict]
        by_cases hc : a ∈ w₂.Dom
        . simp [PFun.mem_dom] at hc
          have ⟨y, hy⟩ := hc
          have z'' := (right_1 a).2.1 y hy
          simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, true_and]
        . simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, Finset.mem_coe]
          simp [← Finset.mem_coe, (Set.ext_iff.mp w_Dom.symm) a] at hc
          apply Iff.intro
          · intro a_1
            exact False.elim (hc v a_1)
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            exact False.elim (hc w h)

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
