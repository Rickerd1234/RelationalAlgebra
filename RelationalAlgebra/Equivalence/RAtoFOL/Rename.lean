import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi f q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.r_def.mp (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: RA.Query.isWellTyped dbi.schema q → ∀t, (ra_to_fol_query q dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.r f q) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.r f q) := by
      sorry

theorem ra_to_fol_evalT.r_def.mpr (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih : RA.Query.isWellTyped dbi.schema q → ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeDom dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.r f q) → (ra_to_fol_query (.r f q) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.r f q) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.r f q) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        RA.Query.isWellTyped.r_def, RA.Query.evaluateT.r_def, renameT, exists_eq_right',
        Set.mem_setOf_eq, forall_const, and_self, implies_true]
      obtain ⟨left, right⟩ := h
      sorry
