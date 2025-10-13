import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi a b p q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.s_def.mp (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih: ∀t, (ra_to_fol_query q dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.s a b q) dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.s a b q) := by
      intro t
      simp only [RA.Query.isWellTyped.s_def, ra_to_fol_query, FOL.outVar.def,
        FOL.Query.RealizeMin.def, FOL.BoundedQuery.Realize.def, FOL.BoundedQuery.toFormula_tEq,
        FirstOrder.Language.BoundedFormula.realize_inf, FOL.BoundedQuery.schema.tEq_def,
        RA.Query.evaluateT.s_def, selectionT, ↓reduceIte, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_1 a_2 a_3
      simp_all only [FOL.Query.RealizeMin.def, and_imp]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      apply And.intro
      · apply ih
        · exact a_1
        · simp_all [FirstOrder.Language.Term.varFinsetLeft, ra_to_fol_query_schema]
      · exact a_2

theorem ra_to_fol_evalT.s_def.mpr (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.s a b q) → (ra_to_fol_query (.s a b q) dbi.schema).RealizeMin dbi t := by
      intro t h_RA_eval
      apply And.intro ?_
        (by simp_all [RA.Query.evaluate.validSchema (.s a b q) h t h_RA_eval, ra_to_fol_query_schema])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.s_def, FOL.Query.RealizeMin.def,
        FOL.BoundedQuery.Realize.def, ra_to_fol_query_schema, RA.Query.evaluateT.s_def, selectionT,
        ne_eq, ite_true, Set.mem_setOf_eq, FOL.outVar.def, FOL.BoundedQuery.toFormula_tEq,
        FirstOrder.Language.BoundedFormula.realize_inf, true_and]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h_RA_eval
      obtain ⟨left_2, right⟩ := right
      exact right_1

theorem ra_to_fol_evalT.s_def_eq (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih: (ra_to_fol_query q dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (ra_to_fol_query (.s a b q) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.s a b q) := by
      ext t
      apply Iff.intro
      . exact ra_to_fol_evalT.s_def.mp h
          (λ t' => ((Set.ext_iff.mp ih) t').mp)
          t
      . exact ra_to_fol_evalT.s_def.mpr h
          (λ t' => ((Set.ext_iff.mp ih) t').mpr)
          t
