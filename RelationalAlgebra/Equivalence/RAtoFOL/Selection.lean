import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi a b p q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.s_def.mp (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih: ∀t, (ra_to_fol_query q dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.s a b q) dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.s a b q) := by
      intro t
      simp only [RA.Query.isWellTyped, ra_to_fol_query, FOL.outVar.def, FOL.Query.RealizeMin.ex_def,
        FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula_and, FOL.BoundedQuery.toFormula_tEq,
        Pi.default_def, Nat.default_eq_zero, FirstOrder.Language.BoundedFormula.realize_inf,
        FOL.BoundedQuery.schema.and_def, FOL.BoundedQuery.schema.tEq_def,
        FirstOrder.Language.Term.varFinsetLeft, Finset.coe_union, Finset.coe_singleton,
        Set.union_singleton, Set.union_insert, RA.Query.evaluateT, selectionT, Set.mem_setOf_eq,
        forall_exists_index, and_imp] at ⊢ h
      intro a_1 a_2 a_3
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp [ra_to_fol_query_schema, left, left_1, right] at ih a_1
      apply And.intro
      · apply ih
        simp [FOL.Query.RealizeMin.ex_def, ra_to_fol_query_schema left, a_1]
        convert a_2
        simp [ra_to_fol_query_schema, left, left_1, right, Finset.union_subset_iff]
      · simp [FirstOrder.Language.BoundedFormula.Realize] at a_3
        have : (t a).Dom := by simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        have : (t b).Dom := by simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        simp [Part.getOrElse, *] at a_3
        simp_all [Part.ext_iff, Part.mem_eq]

theorem ra_to_fol_evalT.s_def.mpr (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.s a b q) → (ra_to_fol_query (.s a b q) dbi.schema).RealizeMin dbi t := by
      intro t h_RA_eval
      have h_1 := RA.Query.evaluate.validSchema (.s a b q) h t h_RA_eval
      apply Exists.intro
        (by simp_all [h_1, ra_to_fol_query_schema])

      simp only [ra_to_fol_query, FOL.BoundedQuery.Realize]
      simp_all only [RA.Query.isWellTyped, FOL.Query.RealizeMin.ex_def, Pi.default_def, Nat.default_eq_zero,
        RA.Query.evaluateT, FOL.outVar.def]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all [FOL.BoundedQuery.Realize, selectionT]
      apply And.intro
      · have := (ih t h_RA_eval.1).2
        convert this
        simp [ra_to_fol_query_schema left]
      · simp only [FirstOrder.Language.BoundedFormula.Realize,
          FirstOrder.Language.Term.realize_var, Sum.elim_inl]
        exact FOL.TupleToFun.tuple_eq_ext h_RA_eval.2

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
