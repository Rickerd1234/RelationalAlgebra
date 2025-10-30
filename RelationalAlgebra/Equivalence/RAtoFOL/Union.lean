import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi q₁ q₂} [FOL.folStruc dbi (μ := μ)] [Nonempty μ]

theorem ra_to_fol_evalT.u_def_eq (h : RA.Query.isWellTyped dbi.schema (.u q₁ q₂))
  (ih₁ : FOL.Query.evaluateT dbi (ra_to_fol_query q₁ dbi.schema) = RA.Query.evaluateT dbi q₁)
  (ih₂ : FOL.Query.evaluateT dbi (ra_to_fol_query q₂ dbi.schema) = RA.Query.evaluateT dbi q₂) :
    FOL.Query.evaluateT dbi (ra_to_fol_query (q₁.u q₂) dbi.schema) = RA.Query.evaluateT dbi (q₁.u q₂) := by
      simp_all [ra_to_fol_query]
      simp [FOL.Query.evaluateT, FOL.Query.RealizeMin.and_def, FOL.BoundedQuery.Realize, ← ih₁, ← ih₂]
      simp_all [ra_to_fol_query_schema]
      ext t
      unfold FOL.TupleToFun
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      apply Iff.intro
      · intro a
        simp_all only [forall_true_left, true_and]
        obtain ⟨left_2, right_1⟩ := a
        convert right_1 left_2
      · intro a
        cases a with
        | inl h =>
          simp_all only [forall_true_left, true_and]
          obtain ⟨left_2, right_1⟩ := h
          apply Or.inl
          convert right_1 left_2
        | inr h_1 =>
          simp_all only [forall_true_left, true_and]
          obtain ⟨left_2, right_1⟩ := h_1
          apply Or.inr
          convert right_1 left_2
