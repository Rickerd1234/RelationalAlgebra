import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi q nq} [FOL.folStruc dbi (μ := μ)] [Nonempty μ]

theorem ra_to_fol_evalT.d_def_eq (h : RA.Query.isWellTyped dbi.schema (.d q nq))
  (ih : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema q) = RA.Query.evaluateT dbi q)
  (nih : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema nq) = RA.Query.evaluateT dbi nq) :
    FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema (q.d nq)) = RA.Query.evaluateT dbi (q.d nq) := by
      simp_all [ra_to_fol_query]
      simp [FOL.Query.evaluateT, FOL.Query.RealizeMin.and_def, FOL.BoundedQuery.Realize, ← ih,
        ← nih, Set.diff]
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
        . intro x
          convert (h.2 x).2
      . intro h
        apply And.intro h.1.1
        intro x
        apply And.intro
        . convert h.1.2 x
        . convert h.2 x
