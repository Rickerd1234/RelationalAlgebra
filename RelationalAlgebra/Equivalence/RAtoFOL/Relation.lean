import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {rn} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [struc : FOL.folStruc dbi] [Inhabited μ]

/-- One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for a Relation. -/
theorem toFOL.evalT_def.R_def.mp :
    ∀t, (toFOL dbi.schema (.R rn)).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.R rn) := by
      intro t
      simp_all only [FOL.Query.RealizeMin, FOL.BoundedQuery.Realize, toFOL,
        FOL.BoundedQuery.toFormula.eq_1, FirstOrder.Language.BoundedFormula.realize_rel,
        Function.comp_apply, FOL.outVar.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
        FOL.BoundedQuery.schema.R_def, FirstOrder.Language.Term.varFinsetLeft.eq_1,
        Finset.mem_singleton, RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe,
        RA.Query.evaluateT, forall_exists_index]
      intro h a_1
      rw [@FOL.folStruc.RelMap_R] at a_1
      convert a_1
      apply (FOL.ArityToTuple.def_fromIndex h).symm

/-- (Reverse) One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for a Relation. -/
theorem toFOL.evalT_def.R_def.mpr (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
  ∀t, t ∈ RA.Query.evaluateT dbi (.R rn) → (toFOL dbi.schema (.R rn)).RealizeMin dbi t := by
    intro t h_RA_eval
    apply Exists.intro (by simp_all [RA.Query.evaluate.validSchema (.R rn) h t h_RA_eval, toFOL.schema_def])

    simp only [toFOL]
    simp_all only [FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula,
      FirstOrder.Language.BoundedFormula.realize_rel, Function.comp_apply, FOL.outVar.def,
      FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.schema.R_def,
      FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton,
      RM.RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe, FOL.folStruc_apply_RelMap]

    rw [FOL.ArityToTuple.def_fromIndex]
    . exact h_RA_eval

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for a Relation. -/
theorem toFOL.evalT_def.R_def_eq (h : RA.Query.isWellTyped dbi.schema (.R rn)) :
    (toFOL dbi.schema (.R rn)).evaluateT dbi = RA.Query.evaluateT dbi (.R rn) := by
      ext t
      apply Iff.intro
      . exact toFOL.evalT_def.R_def.mp t
      . exact toFOL.evalT_def.R_def.mpr h t
