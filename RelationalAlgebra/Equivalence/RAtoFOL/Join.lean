import RelationalAlgebra.Equivalence.RAtoFOL.Conversion
import RelationalAlgebra.FOL.RealizeProperties

variable {q₁ q₂} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [struc : FOL.folStruc dbi] [Inhabited μ]

/-- One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Join operation. -/
theorem ra_to_fol_evalT.j_def.mp (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁: ∀t, (ra_to_fol_query dbi.schema q₁).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q₁)
  (ih₂: ∀t, (ra_to_fol_query dbi.schema q₂).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q₂) :
    ∀t, (ra_to_fol_query dbi.schema (.j q₁ q₂)).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) := by
      intro t
      simp only [RA.Query.isWellTyped, ra_to_fol_query, FOL.Query.RealizeMin,
        FOL.BoundedQuery.schema.and_def, Finset.coe_union, RA.Query.evaluateT, joinT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq, joinSingleT] at ⊢ h
      simp only [FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula,
        FirstOrder.Language.BoundedFormula.realize_inf, and_imp]
      intro a_2 a_3 a_4
      have h_dom : t.Dom = ↑(q₁.schema dbi.schema) ∪ ↑(q₂.schema dbi.schema) := by
        rw [← ra_to_fol_query_schema h.1, ← ra_to_fol_query_schema h.2]; exact a_2

      have z' : ↑(ra_to_fol_query dbi.schema q₁).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
      use t.restrict z'
      apply And.intro
      . apply ih₁
        . simp_all only [FOL.Query.RealizeMin]
          obtain ⟨left, right⟩ := h
          apply Exists.intro
          · rw [FOL.BoundedQuery.Realize.enlarge]
            exact a_3
            . simp [Set.subset_def, PFun.mem_dom]
            . rfl
            . rfl
            . rfl
            . simp_all only [FOL.BoundedQuery.schema.and_def, Finset.coe_union]

      . have z' : ↑(ra_to_fol_query dbi.schema q₂).schema ⊆ t.Dom := by simp_all [ra_to_fol_query_schema]
        use t.restrict z'
        apply And.intro
        . apply ih₂
          . simp_all only [FOL.Query.RealizeMin]
            obtain ⟨left, right⟩ := h
            apply Exists.intro
            · rw [FOL.BoundedQuery.Realize.enlarge]
              exact a_4
              . simp [Set.subset_def, PFun.mem_dom]
              . rfl
              . rfl
              . rfl
              . simp_all only [FOL.BoundedQuery.schema.and_def, Finset.coe_union]

        . intro a
          simp only [PFun.mem_restrict, Finset.mem_coe, and_imp, not_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          . intro h₁ h₂
            apply Part.eq_none_iff.mpr
            intro v
            by_cases c1 : (a ∈ q₁.schema dbi.schema)
            . simp_all only [FOL.Query.RealizeMin, ra_to_fol_query_schema, forall_exists_index,
              Set.subset_union_left, Set.subset_union_right, forall_const, not_false_eq_true,
              implies_true]
            . by_cases c2 : (a ∈ q₂.schema dbi.schema)
              . simp_all only [FOL.Query.RealizeMin, ra_to_fol_query_schema, forall_exists_index,
                Set.subset_union_left, Set.subset_union_right, not_true_eq_false, implies_true,
                forall_const, not_false_eq_true]
              . by_contra hc
                have z : ¬(a ∈ t.Dom) := by simp [h_dom, c1, c2]
                apply z
                apply Part.dom_iff_mem.mpr
                use v

/-- (Reverse) One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Join operation. -/
theorem ra_to_fol_evalT.j_def.mpr (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁ : ∀t ∈ RA.Query.evaluateT dbi q₁, (ra_to_fol_query dbi.schema q₁).RealizeMin dbi t)
  (ih₂ : ∀t ∈ RA.Query.evaluateT dbi q₂, (ra_to_fol_query dbi.schema q₂).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.j q₁ q₂) → (ra_to_fol_query dbi.schema (.j q₁ q₂)).RealizeMin dbi t := by
      intro t h_RA_eval
      have t_Dom : t.Dom = q₁.schema dbi.schema ∪ q₂.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema (.j q₁ q₂) h t h_RA_eval

      apply Exists.intro (by simp_all [ra_to_fol_query_schema])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.evaluateT, joinT, joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union,
        not_or, not_exists, and_imp, Set.mem_setOf_eq]
      simp_all only [FOL.Query.RealizeMin]

      obtain ⟨left, right⟩ := h
      obtain ⟨w₁, h⟩ := h_RA_eval
      obtain ⟨hw₁, h⟩ := h
      obtain ⟨w₂, h⟩ := h
      obtain ⟨hw₂, right_1⟩ := h
      simp only [FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula,
        FirstOrder.Language.BoundedFormula.realize_inf]
      apply And.intro
      · have w_Dom : w₁.Dom = q₁.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₁ left w₁ hw₁
        have z' : w₁.Dom ⊆ t.Dom := by simp [t_Dom, w_Dom]
        simp_all only [FOL.BoundedQuery.Realize, Finset.coe_union, Set.subset_union_left]
        have z := (ih₁ w₁ hw₁)
        have ⟨h_sub, ht'⟩ : ∃h_sub : w₁.Dom ⊆ t.Dom, t.restrict h_sub = w₁ := by
          simp_all only [Finset.coe_union, Finset.coe_inj, Set.subset_union_left, exists_true_left]
          ext a v; simp [*]
          simp_all only [Finset.coe_union]
          have := Set.ext_iff.mp (RA.Query.evaluate.validSchema q₁ left w₁ hw₁).symm a
          simp only [Finset.mem_coe] at this
          simp only [this, PFun.mem_dom]
          apply Iff.intro
          · intro a_1
            simp_all only [Finset.mem_coe]
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            simp_all [(right_1 a).1 w h]
          · intro a_1
            apply And.intro
            · use v
            · rw [(right_1 a).1 v a_1]
              exact a_1

        rw [← FOL.BoundedQuery.Realize]
        rw [← FOL.BoundedQuery.Realize.enlarge h_sub ht' (by simp [ra_to_fol_query_schema left, w_Dom])]
        . exact z.2
        . simp [ra_to_fol_query_schema left, z.1]
        . simp [t_Dom, ra_to_fol_query_schema left, ra_to_fol_query_schema right]

      · have w_Dom : w₂.Dom = q₂.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₂ right w₂ hw₂
        have z' : w₂.Dom ⊆ t.Dom := by simp [t_Dom, w_Dom]
        simp_all only [FOL.BoundedQuery.Realize, Finset.coe_union]
        have z := (ih₂ w₂ hw₂)
        have ⟨h_sub, ht'⟩ : ∃h_sub : w₂.Dom ⊆ t.Dom, t.restrict h_sub = w₂ := by
          simp_all only [Finset.coe_union, exists_true_left]
          ext a v; simp [*]
          simp_all only [Finset.coe_union]
          have := Set.ext_iff.mp (RA.Query.evaluate.validSchema q₂ right w₂ hw₂).symm a
          simp only [Finset.mem_coe] at this
          simp only [this, PFun.mem_dom]
          apply Iff.intro
          · intro a_1
            simp_all only [Finset.mem_coe]
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            rw [← (right_1 a).2.1 w h]
            exact right_2
          · intro a_1
            apply And.intro
            · use v
            · rw [(right_1 a).2.1 v a_1]
              exact a_1

        rw [← FOL.BoundedQuery.Realize]
        rw [← FOL.BoundedQuery.Realize.enlarge h_sub ht' (by simp [ra_to_fol_query_schema right, w_Dom])]
        . exact z.2
        . simp [ra_to_fol_query_schema right, z.1]
        . simp [t_Dom, ra_to_fol_query_schema left, ra_to_fol_query_schema right]

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Join operation. -/
theorem ra_to_fol_evalT.j_def_eq (h : RA.Query.isWellTyped dbi.schema (.j q₁ q₂))
  (ih₁ : (ra_to_fol_query dbi.schema q₁).evaluateT dbi = RA.Query.evaluateT dbi q₁)
  (ih₂ : (ra_to_fol_query dbi.schema q₂).evaluateT dbi = RA.Query.evaluateT dbi q₂) :
    (ra_to_fol_query dbi.schema (.j q₁ q₂)).evaluateT dbi = RA.Query.evaluateT dbi (.j q₁ q₂) := by
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
