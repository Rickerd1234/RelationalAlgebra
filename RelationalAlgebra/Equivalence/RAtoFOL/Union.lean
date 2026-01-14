import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {q₁ q₂} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Inhabited μ]

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Union operation. -/
theorem ra_to_fol_evalT.u_def_eq (h : RA.Query.isWellTyped dbi.schema (.u q₁ q₂))
  (ih₁ : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema q₁) = RA.Query.evaluateT dbi q₁)
  (ih₂ : FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema q₂) = RA.Query.evaluateT dbi q₂) :
    FOL.Query.evaluateT dbi (ra_to_fol_query dbi.schema (q₁.u q₂)) = RA.Query.evaluateT dbi (q₁.u q₂) := by
      simp_all only [ra_to_fol_query]
      simp [FOL.Query.evaluateT, FOL.Query.RealizeMin.and_def, FOL.BoundedQuery.Realize, ← ih₁, ← ih₂]
      simp_all [ra_to_fol_query_schema]
      ext t
      unfold FOL.TupleToFun
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      grind only [cases Or]
