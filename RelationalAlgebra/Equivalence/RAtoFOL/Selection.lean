import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi a b p q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.s_def.mp (h : RA.Query.isWellTyped dbi.schema (.s a b p q))
  (ih: RA.Query.isWellTyped dbi.schema q → ∀t, (ra_to_fol_query q dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.s a b p q) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.s a b p q) := by
      intro t
      simp [RA.Query.isWellTyped.s_def, ra_to_fol_query, FOL.outVar.def,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.Realize.tEq_def, FOL.Term.realizeSome.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.schema.tEq_def,
        RA.Query.evaluateT.s_def, selectionT, ↓reduceIte, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_4 a_5 a_6 a_7 a_8
      simp_all [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]
      exact a_7

theorem ra_to_fol_evalT.s_def.mpr (h : RA.Query.isWellTyped dbi.schema (.s a b p q))
  (ih : RA.Query.isWellTyped dbi.schema q → ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeDom dbi t):
    ∀t, t ∈ RA.Query.evaluateT dbi (.s a b p q) → (ra_to_fol_query (.s a b p q) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.s a b p q) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.s a b p q) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.s_def, FOL.Query.RealizeDom.def,
        ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, forall_const, RA.Query.evaluateT.s_def,
        selectionT, ne_eq, ite_true, Set.mem_setOf_eq, FOL.outVar.def,
        FOL.BoundedQuery.Realize.tEq_def, FOL.Term.realizeSome.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, and_self_left, true_and]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h_RA_eval
      obtain ⟨left_2, right⟩ := right
      apply And.intro
      · have z : ∀x, x ∈ q.schema dbi.schema ↔ (t x).Dom := by
          simp [(RA.Query.evaluate dbi q left).validSchema t left_1, RA.Query.evaluate, Part.dom_iff_mem, ← PFun.mem_dom]
        simp_all only
      · exact right_1
