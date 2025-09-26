import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rn} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.R_def.mp :
    ∀t, (ra_to_fol_query (.R rn) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.R rn) := by
      intro t
      simp_all only [ra_to_fol_query, FOL.Query.RealizeDom.def, FOL.BoundedQuery.Realize.def,
        FOL.BoundedQuery.toFormula_rel, FirstOrder.Language.BoundedFormula.realize_rel,
        Function.comp_apply, FOL.outVar.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
        FOL.folStruc_apply_RelMap, FOL.BoundedQuery.schema.R_def,
        FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton,
        RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe, RA.Query.evaluateT.R_def, and_imp]
      intro a a_1
      rw [FOL.ArityToTuple.def_fromIndex t] at a
      . exact a
      . exact a_1

theorem ra_to_fol_evalT.R_def.mpr (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
  ∀t, t ∈ RA.Query.evaluateT dbi (.R rn) → (ra_to_fol_query (.R rn) dbi.schema).RealizeDom dbi t := by
    intro t h_RA_eval
    apply And.intro ?_
      (by simp_all [RA.Query.evaluate.validSchema (.R rn) h t h_RA_eval, ra_to_fol_query_schema])

    simp only [ra_to_fol_query]
    simp_all only [RA.Query.isWellTyped.R_def, RA.Query.evaluateT.R_def,
      FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_rel,
      FirstOrder.Language.BoundedFormula.realize_rel, Function.comp_apply, FOL.outVar.def,
      FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.folStruc_apply_RelMap]

    rw [FOL.ArityToTuple.def_fromIndex t]
    . exact h_RA_eval
    . simp [RM.RelationInstance.validSchema.def h_RA_eval]

theorem ra_to_fol_evalT.R_def_eq (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
    (ra_to_fol_query (.R rn) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.R rn) := by
      ext t
      apply Iff.intro
      . exact ra_to_fol_evalT.R_def.mp t
      . exact ra_to_fol_evalT.R_def.mpr h t
