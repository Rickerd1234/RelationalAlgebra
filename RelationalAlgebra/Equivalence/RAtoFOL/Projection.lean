import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rs q} [FOL.folStruc dbi]

theorem ra_to_fol_evalT.p_def.mp (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih: RA.Query.isWellTyped dbi.schema q → ∀t, (ra_to_fol_query q dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.p rs q) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.p rs q) := by
      intro t
      simp only [RA.Query.isWellTyped.p_def, ra_to_fol_query, projectQuery.def, Nat.add_zero,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.schema.exs_def, FOL.BoundedQuery.relabel_schema,
        Finset.coe_pimage, RA.Query.evaluateT.p_def, projectionT, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_2 a_3
      obtain ⟨left, right⟩ := h
      have h_rs : ↑rs ⊆ t.Dom := by sorry
      use t.restrict h_rs
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
        forall_const, projectAttribute]
      apply And.intro
      · apply ih
        . sorry
        . exact right
      · intro a
        apply And.intro
        · intro a_1
          simp_all
          ext v : 1
          simp_all only [ra_to_fol_query.isWellTyped, PFun.mem_restrict, Finset.mem_coe, true_and]
        · intro a_1
          sorry

theorem ra_to_fol_evalT.p_def.mpr (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih : RA.Query.isWellTyped dbi.schema q → ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeDom dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.p rs q) → (ra_to_fol_query (.p rs q) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      have t_Dom : t.Dom = rs := by
        exact RA.Query.evaluate.validSchema (.p rs q) h t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.p rs q) dbi.schema)
          (by simp_all)

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.p_def, RA.Query.evaluateT.p_def, projectionT,
        Set.mem_setOf_eq, forall_const]
      simp_all only [projectQuery.def, Nat.add_zero]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := h_RA_eval
      obtain ⟨hw, right_1⟩ := h

      have z := (ih w hw)
      have w_Dom : w.Dom = q.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema q left w hw

      sorry
