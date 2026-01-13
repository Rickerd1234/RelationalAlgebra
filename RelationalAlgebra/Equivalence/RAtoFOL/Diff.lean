import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {q nq} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Nonempty μ]

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Difference operation. -/
theorem ra_to_fol_evalT.d_def_eq (h : RA.Query.isWellTyped dbi.schema (.d q nq))
  (ih : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema q) = RA.Query.evaluateT dbi q)
  (nih : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema nq) = RA.Query.evaluateT dbi nq) :
    FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema (q.d nq)) = RA.Query.evaluateT dbi (q.d nq) := by
      simp_all only [RA.Query.isWellTyped, ra_to_fol_query, RA.Query.evaluateT, differenceT]
      simp only [FOL.Query.evaluateT, FOL.Query.RealizeMin.and_def, FOL.BoundedQuery.schema.and_def,
        FOL.BoundedQuery.schema.not_def, Finset.coe_union, FOL.BoundedQuery.Realize,
        FOL.BoundedQuery.toFormula, FirstOrder.Language.BoundedFormula.realize_inf,
        FirstOrder.Language.BoundedFormula.realize_not, ← ih, ← nih]
      simp_all [ra_to_fol_query_schema]
      ext t
      unfold FOL.TupleToFun
      simp_all only [Set.mem_setOf_eq]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      apply Iff.intro
      . intro h
        apply And.intro
        . apply And.intro h.1
          intro x
          convert (h.2 x).1
        . simp only [Set.mem_setOf_eq, not_and, not_forall]
          intro x
          use x
          convert (h.2 x).2
      . intro h
        apply And.intro h.1.1
        intro x
        apply And.intro
        . convert h.1.2 x
        . simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_forall] at h
          convert (h.2 x).2
