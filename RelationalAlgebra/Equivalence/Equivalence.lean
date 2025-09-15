import RelationalAlgebra.Equivalence.RAtoFOL.Defs

open RM

@[simp]
theorem ra_to_fol_evalT.FOL_evaluateT (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) :
  t ∈ (ra_to_fol_query raQ dbi.schema).evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    simp_all only [FOL.Query.evaluateT, FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
      FOL.BoundedQuery.RealizeValidDom.def, IsEmpty.forall_iff,
      DatabaseInstance.default_ran_sub_domain, and_self, and_true, Set.mem_setOf_eq]

-- @TODO: Split this over multiple smaller proofs
theorem ra_to_fol_evalT.reverse {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn =>
      intro t
      simp_all only [RA.Query.isWellTyped.R_def, ra_to_fol_query, FOL.Query.RealizeDom.def,
        FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.Realize.R_def, Function.comp_apply,
        FOL.outVar.def, FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var,
        Sum.elim_inl, FOL.BoundedQuery.toFormula_rel,
        FirstOrder.Language.BoundedFormula.realize_rel, FOL.folStruc_apply_RelMap,
        FOL.BoundedQuery.RealizeValidDom.def, FOL.BoundedQuery.schema.R_def,
        FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton,
        RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe, IsEmpty.forall_iff,
        DatabaseInstance.default_ran_sub_domain, and_self, and_true, RA.Query.evaluateT.R_def,
        and_imp]
      intro a a_1 a_2 a_3 a_4
      simp_all only [RelationSchema.fromIndex_mem, implies_true]
      rw [FOL.ArityToTuple.def_fromIndex t] at a_1
      . exact a_1
      . exact a_4

    | s a b p sq ih =>
      intro t
      simp only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
        FOL.BoundedQuery.RealizeValidDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        IsEmpty.forall_iff, DatabaseInstance.default_ran_sub_domain, and_self, and_true, and_imp,
        RA.Query.isWellTyped.s_def, ra_to_fol_query, FOL.outVar.def,
        FOL.BoundedQuery.Realize.tEq_def, FOL.Term.realizeSome.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.schema.tEq_def,
        RA.Query.evaluateT.s_def, selectionT, ne_eq, ite_true, Set.mem_setOf_eq, implies_true,
        true_and, forall_const] at ⊢ h
      intro a_4 a_5 a_6 a_7 a_8 a_9 a_10
      simp_all only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
        FOL.BoundedQuery.RealizeValidDom.def, IsEmpty.forall_iff,
        DatabaseInstance.default_ran_sub_domain, and_self, and_true, and_imp, forall_const,
        implies_true, true_and]
      exact a_7

    | p rs sq ih =>
      intro t
      simp only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
        FOL.BoundedQuery.RealizeValidDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        IsEmpty.forall_iff, DatabaseInstance.default_ran_sub_domain, and_self, and_true, and_imp,
        RA.Query.isWellTyped.p_def, ra_to_fol_query, projectQuery.def, Nat.add_zero,
        FOL.BoundedQuery.schema.exs_def, FOL.BoundedQuery.relabel_schema, Finset.mem_pimage,
        Part.mem_ofOption, Option.mem_def, Sum.getLeft?_eq_some_iff, forall_exists_index,
        Finset.coe_pimage, RA.Query.evaluateT.p_def, projectionT, Set.mem_setOf_eq, forall_const,
        implies_true] at ⊢ h
      intro a_2 a_3 a_4 a_5
      obtain ⟨left, right⟩ := h
      use t
      simp_all only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.RealizeValidDom.def,
        ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, IsEmpty.forall_iff,
        DatabaseInstance.default_ran_sub_domain, and_self, and_true, and_imp, forall_const, implies_true, true_and]
      apply And.intro
      · apply ih
        . sorry
        . sorry
        . sorry
        . sorry
      · intro a a_1
        sorry

    | j q₁ q₂ ih₁ ih₂ =>
      intro t
      simp only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
        FOL.BoundedQuery.RealizeValidDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        IsEmpty.forall_iff, DatabaseInstance.default_ran_sub_domain, and_self, and_true, and_imp,
        RA.Query.isWellTyped.j_def, ra_to_fol_query, FOL.BoundedQuery.Realize.and_def,
        FOL.BoundedQuery.schema.and_def, Finset.mem_union, Finset.coe_union, RA.Query.evaluateT.j_def,
        joinT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, Set.mem_setOf_eq,
        forall_const, implies_true] at ⊢ h
      intro a_2 a_3 a_4 a_5 a_6
      have h_dom : t.Dom = ↑(q₁.schema dbi.schema) ∪ ↑(q₂.schema dbi.schema) := by
        simp [h] at a_6 a_4
        obtain ⟨left, right⟩ := h
        exact Set.Subset.antisymm a_6 a_4

      have z' : ↑(q₁.schema dbi.schema) ⊆ t.Dom := by simp_all
      use t.restrict (z')
      apply And.intro
      . apply ih₁
        . exact h.1
        . sorry

      . have z' : ↑(q₂.schema dbi.schema) ⊆ t.Dom := by simp_all
        use t.restrict (z')
        apply And.intro
        . apply ih₂
          . exact h.2
          . sorry

        . intro a
          simp only [PFun.mem_restrict, Finset.mem_coe, and_imp, not_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only [Set.subset_union_right]
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          apply And.intro
          . intro x a_1 a_7
            simp_all only [Set.subset_union_left]
            obtain ⟨left, right⟩ := h
            ext a_6 : 1
            simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
          . intro h₁ h₂
            apply Part.eq_none_iff.mpr
            intro v
            by_cases c1 : (a ∈ q₁.schema dbi.schema)
            . aesop
            . by_cases c2 : (a ∈ q₂.schema dbi.schema)
              . aesop
              . by_contra hc
                have z : ¬(a ∈ t.Dom) := by simp [h_dom, c1, c2]
                apply z
                apply Part.dom_iff_mem.mpr
                use v

    | r => sorry

theorem ra_to_fol_evalT.mem (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema):
  ∀t, t ∈ raQ.evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    intro t
    apply Iff.intro
    . intro h_RA_eval
      apply
        FOL.Query.RealizeDom.isWellTyped_eq_Realize
          (ra_to_fol_query raQ dbi.schema)
          (ra_to_fol_query.isWellTyped raQ dbi.schema h_ra_wt)
          (by simp_all [RA.Query.evaluate.validSchema raQ h_ra_wt t h_RA_eval])
          (RA.Query.evaluateT.dbi_domain h_ra_wt t h_RA_eval)


      induction raQ with
      | R rn =>
        simp only [ra_to_fol_query]
        simp_all only [RA.Query.isWellTyped.R_def, RA.Query.evaluateT.R_def,
          FOL.BoundedQuery.Realize.R_def, Function.comp_apply, FOL.outVar.def,
          FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
          RelationSchema.fromIndex_Dom, implies_true, FOL.BoundedQuery.toFormula_rel,
          FirstOrder.Language.BoundedFormula.realize_rel, FOL.folStruc_apply_RelMap, true_and]

        rw [FOL.ArityToTuple.def_fromIndex t]
        . exact h_RA_eval
        . sorry

      | _ => simp_all [ra_to_fol_query, selectionT, projectionT, joinT, renameT]; sorry

    . exact ra_to_fol_evalT.reverse h_ra_wt t

theorem ra_to_fol_eval {dbi} [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema) :
  raQ.evaluate dbi h_ra_wt = (ra_to_fol_query raQ dbi.schema).evaluate dbi := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    simp_all
    ext t
    simp_all only [ra_to_fol_evalT.FOL_evaluateT]
    exact ra_to_fol_evalT.mem dbi raQ h_ra_wt t

theorem ra_to_fol {dbi} [FOL.folStruc dbi] (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.Query, raQ.evaluate dbi h = folQ.evaluate dbi := by
    use ra_to_fol_query raQ dbi.schema
    exact ra_to_fol_eval raQ h


theorem fol_to_ra {dbi} [FOL.folStruc dbi] (folQ : FOL.Query) (h : folQ.isWellTyped) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
