import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {a b p q} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [struc : FOL.folStruc dbi] [Inhabited μ]

/-- One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Selection operation. -/
theorem toFOL.evalT_def.s_def.mp (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih: ∀t, (toFOL dbi.schema q).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (toFOL dbi.schema (.s a b q)).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.s a b q) := by
      intro t
      simp only [RA.Query.isWellTyped, toFOL, FOL.freeVar.def, FOL.Query.RealizeMin.ex_def,
        FOL.BoundedQuery.Realize, FOL.BoundedQuery.toFormula,
        FirstOrder.Language.BoundedFormula.realize_inf, FOL.BoundedQuery.schema.and_def,
        FOL.BoundedQuery.schema.tEq_def, FirstOrder.Language.Term.varFinsetLeft, Finset.coe_union,
        Finset.coe_singleton, Set.union_singleton, Set.union_insert, RA.Query.evaluateT, selectionT,
        Set.mem_setOf_eq, forall_exists_index, and_imp] at ⊢ h
      intro a_1 a_2 a_3
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp [toFOL.schema_def, left, left_1, right] at ih a_1
      apply And.intro
      · apply ih
        simp only [FOL.Query.RealizeMin.ex_def, a_1, Finset.coe_inj, toFOL.schema_def left,
          exists_true_left, FOL.TupleToFun.tuple_eq_self]
        convert a_2
        simp [toFOL.schema_def, left, left_1, right]
      · simp [FirstOrder.Language.BoundedFormula.Realize] at a_3
        have : (t a).Dom := by simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        have : (t b).Dom := by simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        simp [Part.getOrElse, *] at a_3
        simp_all [Part.ext_iff, Part.mem_eq]

/-- (Reverse) One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Selection operation. -/
theorem toFOL.evalT_def.s_def.mpr (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (toFOL dbi.schema q).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.s a b q) → (toFOL dbi.schema (.s a b q)).RealizeMin dbi t := by
      intro t h_RA_eval
      have h_1 := RA.Query.evaluate.validSchema (.s a b q) h t h_RA_eval
      apply Exists.intro
        (by simp_all [toFOL.schema_def])

      simp only [toFOL, FOL.BoundedQuery.Realize]
      simp_all only [FOL.Query.RealizeMin.ex_def, RA.Query.evaluateT, FOL.freeVar.def]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all [FOL.BoundedQuery.Realize, selectionT]
      apply And.intro
      · have := (ih t h_RA_eval.1).2
        convert this
        simp [toFOL.schema_def left]
      · simp only [FirstOrder.Language.BoundedFormula.Realize,
          FirstOrder.Language.Term.realize_var, Sum.elim_inl]
        exact FOL.TupleToFun.tuple_eq_ext h_RA_eval.2

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Selection operation. -/
theorem toFOL.evalT_def.s_def_eq (h : RA.Query.isWellTyped dbi.schema (.s a b q))
  (ih: (toFOL dbi.schema q).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (toFOL dbi.schema (.s a b q)).evaluateT dbi = RA.Query.evaluateT dbi (.s a b q) := by
      ext t
      apply Iff.intro
      . exact toFOL.evalT_def.s_def.mp h
          (λ t' => ((Set.ext_iff.mp ih) t').mp)
          t
      . exact toFOL.evalT_def.s_def.mpr h
          (λ t' => ((Set.ext_iff.mp ih) t').mpr)
          t
