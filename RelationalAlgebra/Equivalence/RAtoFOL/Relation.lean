import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rn} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.R_def.mp :
    ∀t, (ra_to_fol_query (.R rn) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.R rn) := by
      intro t
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        ra_to_fol_query, Nat.add_zero, FOL.BoundedQuery.relabel.R_def, Function.comp_apply,
        FOL.outVar.def, FirstOrder.Language.Term.relabel.eq_1, FOL.BoundedQuery.isWellTyped.R_def,
        FOL.BoundedQuery.Realize.R_def, FOL.Term.realizeSome.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.toFormula_rel,
        FirstOrder.Language.BoundedFormula.realize_rel, FOL.folStruc_apply_RelMap,
        FOL.BoundedQuery.schema.R_def, FirstOrder.Language.Term.varFinsetLeft.eq_1,
        Finset.mem_singleton, RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe,
        RA.Query.evaluateT.R_def, and_imp]
      intro a a_1 a_2
      rw [FOL.ArityToTuple.def_fromIndex t] at a_1
      . exact a_1
      . exact a_2

theorem ra_to_fol_evalT.R_def.mpr (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
  ∀t, t ∈ RA.Query.evaluateT dbi (.R rn) → (ra_to_fol_query (.R rn) dbi.schema).RealizeDom dbi t := by
    intro t h_RA_eval
    apply
      FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
        (ra_to_fol_query (.R rn) dbi.schema)
        (by simp_all [RA.Query.evaluate.validSchema (.R rn) h t h_RA_eval])

    simp only [ra_to_fol_query]
    simp_all only [RA.Query.isWellTyped.R_def, RA.Query.evaluateT.R_def,
      FOL.BoundedQuery.Realize.R_def, Function.comp_apply, FOL.outVar.def,
      FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
      RM.RelationSchema.fromIndex_Dom, implies_true, FOL.BoundedQuery.toFormula_rel,
      FirstOrder.Language.BoundedFormula.realize_rel, FOL.folStruc_apply_RelMap, true_and]

    rw [FOL.ArityToTuple.def_fromIndex t]
    . exact h_RA_eval
    . simp [RM.RelationInstance.validSchema.def h_RA_eval]
