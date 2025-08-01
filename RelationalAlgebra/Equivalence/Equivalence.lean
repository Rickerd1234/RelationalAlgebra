import RelationalAlgebra.Equivalence.RAtoFOL.Defs

open RM

theorem ra_to_fol_eval [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  raQ.evaluate dbi h = (ra_to_fol_def raQ h).evaluate := by
    simp [FOL.EvaluableQuery.evaluate, RA.Query.evaluate, FOL.EvaluableQuery.schema]
    apply And.intro
    . simp [ra_to_fol_outFn_eq_schema h, ra_to_fol_def]
    . induction raQ
      all_goals (
        simp only [RA.Query.isWellTyped] at h
        simp only [ra_to_fol_def]
        simp_all only [RA.Query.evaluateT, FOL.EvaluableQuery.evaluateT, ra_to_fol_query_def,
          ra_to_fol_outFn_def, id_eq]
        unfold FOL.VariableAssignmentToTuple
        simp
      )
      case R rn =>
        . ext t
          simp_all only [Set.mem_setOf_eq]
          apply Iff.intro
          · intro ht
            use λ v => t v
            apply And.intro
            · simp_all [FOL.BoundedQuery.RealizeDom, FOL.Query.Realize]
              apply And.intro
              · simp_all [FOL.BoundedQuery.toFormula]
                sorry
              . simp_all [PFun.ran, DatabaseInstance.domain]
                intro v a h
                use rn
                use a
                use t
                simp_all only [Part.eq_some_iff, true_and]
            · simp_all [PFun.res, PFun.restrict, Part.restrict, Part.bind]
              ext a v
              simp_all only [Part.mem_assert_iff, Finset.mem_coe, exists_prop, iff_and_self]
              intro a_1
              rw [DatabaseInstance.validSchema]
              have hz : a ∈ t.Dom → a ∈ (dbi.relations rn).schema := by simp [(dbi.relations rn).validSchema t ht]
              apply hz
              apply (PFun.mem_dom t a).mpr
              use v
          · intro a
            obtain ⟨w, h⟩ := a
            obtain ⟨left, right⟩ := h
            subst right
            sorry
      case s a b posEq sq ih =>
        . simp_all [selectionT]
          sorry
      case p rs sq ih =>
        simp_all [ra_to_fol_query_p, ra_to_fol_outFn_p, projectionT]
        ext t
        simp_all only [Set.mem_setOf_eq]
        sorry
      case r f sq ih =>
        simp_all only [forall_true_left, renameT, exists_eq_right', ra_to_fol_query_r,
          ra_to_fol_outFn_r, Function.comp_apply]
        ext t
        simp_all only [forall_true_left, Set.mem_setOf_eq]
        obtain ⟨left, right⟩ := h
        apply Iff.intro
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_1, right_1⟩ := h
          use w
          sorry
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_1, right_1⟩ := h
          subst right_1
          sorry
      all_goals sorry

theorem ra_to_fol [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.EvaluableQuery dbi.schema, raQ.evaluate dbi h = folQ.evaluate dbi := by
    use ra_to_fol_def raQ h
    simp [ra_to_fol_eval]


theorem fol_to_ra [FOL.folStruc] {dbi} (folQ : FOL.EvaluableQuery dbi.schema) :
  ∃raQ : RA.Query, (h : raQ.isWellTyped dbi.schema) → raQ.evaluate dbi h = folQ.evaluate dbi := by sorry
