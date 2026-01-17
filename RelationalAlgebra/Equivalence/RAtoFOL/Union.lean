import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {q₁ q₂} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Inhabited μ]

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Union operation. -/
theorem toFOL_evalT.u_def_eq (h : RA.Query.isWellTyped dbi.schema (.u q₁ q₂))
  (ih₁ : FOL.Query.evaluateT dbi (toFOL dbi.schema q₁) = RA.Query.evaluateT dbi q₁)
  (ih₂ : FOL.Query.evaluateT dbi (toFOL dbi.schema q₂) = RA.Query.evaluateT dbi q₂) :
    FOL.Query.evaluateT dbi (toFOL dbi.schema (q₁.u q₂)) = RA.Query.evaluateT dbi (q₁.u q₂) := by
      rw [toFOL]
      rw [RA.Query.isWellTyped] at h
      simp [*, toFOL_schema, FOL.Query.evaluateT, FOL.Query.RealizeMin.and_def, FOL.BoundedQuery.Realize, ← ih₁, ← ih₂]
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_union, imp_iff_not_or]

      by_cases h : t.Dom = ↑(q₂.schema dbi.schema)
      . unfold FOL.TupleToFun
        simp only [h, not_not, forall_true_left, true_and]
        grind only [cases Or]
      . simp only [h, not_not, IsEmpty.forall_iff, and_true, or_self]
