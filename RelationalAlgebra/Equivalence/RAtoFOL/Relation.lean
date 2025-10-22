import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rn} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.R_def.mp :
    ∀t, (ra_to_fol_query (.R rn) dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.R rn) := by
      intro t
      simp_all only [FOL.Query.RealizeMin, FOL.BoundedQuery.Realize, ra_to_fol_query,
        FOL.BoundedQuery.toFormula.eq_1, FOL.fol.Rel, Pi.default_def, Nat.default_eq_zero,
        FirstOrder.Language.BoundedFormula.realize_rel, Function.comp_apply, FOL.outVar.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.schema.R_def,
        FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton,
        RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe, RA.Query.evaluateT,
        forall_exists_index]
      intro h a_1
      rw [@FOL.folStruc.RelMap_R] at a_1
      convert a_1
      apply (FOL.ArityToTuple.def_fromIndex h).symm

theorem ra_to_fol_evalT.R_def.mpr (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
  ∀t, t ∈ RA.Query.evaluateT dbi (.R rn) → (ra_to_fol_query (.R rn) dbi.schema).RealizeMin dbi t := by
    intro t h_RA_eval
    apply Exists.intro (by simp_all [RA.Query.evaluate.validSchema (.R rn) h t h_RA_eval, ra_to_fol_query_schema])

    simp only [ra_to_fol_query]
    simp_all only [FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula, Pi.default_def,
      Nat.default_eq_zero, FirstOrder.Language.BoundedFormula.realize_rel, Function.comp_apply,
      FOL.outVar.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
      FOL.BoundedQuery.schema.R_def, FirstOrder.Language.Term.varFinsetLeft.eq_1,
      Finset.mem_singleton, RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe,
      FOL.folStruc_apply_RelMap]

    rw [FOL.ArityToTuple.def_fromIndex]
    . exact h_RA_eval

theorem ra_to_fol_evalT.R_def_eq (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
    (ra_to_fol_query (.R rn) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.R rn) := by
      ext t
      apply Iff.intro
      . exact ra_to_fol_evalT.R_def.mp t
      . exact ra_to_fol_evalT.R_def.mpr h t
