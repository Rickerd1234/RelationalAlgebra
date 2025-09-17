import RelationalAlgebra.Equivalence.RAtoFOL.Defs

open RM

@[simp]
theorem ra_to_fol_evalT.FOL_evaluateT (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) :
  t ∈ (ra_to_fol_query raQ dbi.schema).evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    simp_all only [FOL.Query.evaluateT, FOL.Query.RealizeDom.def, Set.mem_setOf_eq]

-- @TODO: Split this over multiple smaller proofs
theorem ra_to_fol_evalT.fr {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn =>
      intro t
      simp_all only [RA.Query.isWellTyped.R_def, ra_to_fol_query, FOL.Query.RealizeDom.def,
        FOL.BoundedQuery.Realize.R_def, Function.comp_apply, FOL.outVar.def,
        FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
        FOL.BoundedQuery.toFormula_rel, FirstOrder.Language.BoundedFormula.realize_rel,
        FOL.folStruc_apply_RelMap, FOL.BoundedQuery.schema.R_def,
        FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton,
        RelationSchema.Dom_sub_fromIndex, Finset.toFinset_coe, RA.Query.evaluateT.R_def, and_imp]
      intro a a_1 a_2
      rw [FOL.ArityToTuple.def_fromIndex t] at a_1
      . exact a_1
      . exact a_2

    | s a b p sq ih =>
      intro t
      simp only [RA.Query.isWellTyped.s_def, ra_to_fol_query, FOL.outVar.def,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.Realize.tEq_def, FOL.Term.realizeSome.def,
        FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.schema.tEq_def,
        RA.Query.evaluateT.s_def, selectionT, ne_eq, ite_true, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_4 a_5 a_6 a_7 a_8
      simp_all only [FOL.Query.RealizeDom.def, and_imp, forall_const, true_and]
      exact a_7

    | p rs sq ih =>
      intro t
      simp only [RA.Query.isWellTyped.p_def, ra_to_fol_query, projectQuery.def, Nat.add_zero,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.schema.exs_def, FOL.BoundedQuery.relabel_schema,
        Finset.coe_pimage, RA.Query.evaluateT.p_def, projectionT, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_2 a_3
      obtain ⟨left, right⟩ := h
      have h_rs : ↑rs ⊆ t.Dom := by sorry
      use t.restrict h_rs
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
        forall_const]
      apply And.intro
      · sorry
      · intro a
        apply And.intro
        · intro a_1
          sorry
        · intro a_1
          sorry

    | j q₁ q₂ ih₁ ih₂ =>
      intro t
      simp only [RA.Query.isWellTyped.j_def, ra_to_fol_query, FOL.Query.RealizeDom.def,
        FOL.BoundedQuery.Realize.and_def, FOL.BoundedQuery.schema.and_def, Finset.coe_union,
        RA.Query.evaluateT.j_def, joinT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or,
        not_exists, and_imp, Set.mem_setOf_eq] at ⊢ h
      intro a_2 a_3 a_4
      have h_dom : t.Dom = ↑(q₁.schema dbi.schema) ∪ ↑(q₂.schema dbi.schema) := by
        simp [h] at a_4
        obtain ⟨left, right⟩ := h

        have z₁ := FOL.BoundedQuery.Realize.schema_sub_Dom a_2
        have z₂ := FOL.BoundedQuery.Realize.schema_sub_Dom a_3
        simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
          forall_const]

        apply Set.Subset.antisymm a_4 (Set.union_subset z₁ z₂)

      have z' : ↑(ra_to_fol_query q₁ dbi.schema).schema ⊆ t.Dom := by simp_all
      use t.restrict (z')
      apply And.intro
      . apply ih₁
        . exact h.1
        . apply And.intro
          . exact FOL.BoundedQuery.Realize.tuple_restrict2 (by simp [h.1]) z' a_2
          . simp_all
            simp [PFun.Dom, Part.dom_iff_mem, z', Set.subset_def]
            aesop

      . have z' : ↑(ra_to_fol_query q₂ dbi.schema).schema ⊆ t.Dom := by simp_all
        use t.restrict (z')
        apply And.intro
        . apply ih₂
          . exact h.2
          . apply And.intro
            . exact FOL.BoundedQuery.Realize.tuple_restrict2 (by simp [h.2]) z' a_3
            . simp_all
              simp [PFun.Dom, Part.dom_iff_mem, z', Set.subset_def]
              aesop

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

theorem ra_to_fol_evalT.rf {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, t ∈ RA.Query.evaluateT dbi raQ → (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    induction raQ with
    | R rn =>
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.R rn) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.R rn) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.R_def, RA.Query.evaluateT.R_def,
        FOL.BoundedQuery.Realize.R_def, Function.comp_apply, FOL.outVar.def,
        FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
        RelationSchema.fromIndex_Dom, implies_true, FOL.BoundedQuery.toFormula_rel,
        FirstOrder.Language.BoundedFormula.realize_rel, FOL.folStruc_apply_RelMap, true_and]

      rw [FOL.ArityToTuple.def_fromIndex t]
      . exact h_RA_eval
      . simp [RelationInstance.validSchema.def h_RA_eval]

    | s a b p sq ih =>
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.s a b p sq) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.s a b p sq) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.s_def, RA.Query.evaluateT.s_def, selectionT, ne_eq,
        ite_true, Set.mem_setOf_eq, FOL.outVar.def, FOL.BoundedQuery.Realize.tEq_def,
        FOL.Term.realizeSome.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
        and_self_left, true_and, forall_const]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, true_and]
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h_RA_eval
      obtain ⟨left_2, right⟩ := right
      apply And.intro
      · have z : ∀x, x ∈ sq.schema dbi.schema ↔ (t x).Dom := by
          simp [(RA.Query.evaluate dbi sq left).validSchema t left_1, RA.Query.evaluate, Part.dom_iff_mem, ← PFun.mem_dom]
        simp_all only
      · exact right_1

    | p rs sq ih =>
      intro t h_RA_eval
      have t_Dom : t.Dom = rs := by
        exact RA.Query.evaluate.validSchema (.p rs sq) h t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.p rs sq) dbi.schema)
          (by simp_all)

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.p_def, RA.Query.evaluateT.p_def, projectionT,
        Set.mem_setOf_eq, forall_const]
      simp_all only [projectQuery.def, Nat.add_zero]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := h_RA_eval
      obtain ⟨hw, right_1⟩ := h

      have z := (ih w hw)
      have w_Dom : w.Dom = sq.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema sq left w hw

      sorry

    | j q₁ q₂ ih₁ ih₂ =>
      intro t h_RA_eval
      have t_Dom : t.Dom = q₁.schema dbi.schema ∪ q₂.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema (.j q₁ q₂) h t h_RA_eval

      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.j q₁ q₂) dbi.schema)
          (by simp_all)

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.j_def, RA.Query.evaluateT.j_def, joinT, PFun.mem_dom,
        forall_exists_index, Set.mem_union, not_or, not_exists, and_imp, Set.mem_setOf_eq,
        FOL.BoundedQuery.Realize.and_def, forall_const]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]

      obtain ⟨left, right⟩ := h
      obtain ⟨w₁, h⟩ := h_RA_eval
      obtain ⟨hw₁, h⟩ := h
      obtain ⟨w₂, h⟩ := h
      obtain ⟨hw₂, right_1⟩ := h
      apply And.intro
      · have z := (ih₁ w₁ hw₁)
        have w_Dom : w₁.Dom = q₁.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₁ left w₁ hw₁
        have z' : w₁.Dom ⊆ t.Dom := by simp_all
        apply FOL.BoundedQuery.Realize.tuple_restrict (ra_to_fol_query.isWellTyped q₁ dbi.schema left) z.1 z'

        ext a v
        simp [PFun.mem_restrict]
        by_cases hc : a ∈ w₁.Dom
        . simp [PFun.mem_dom] at hc
          have ⟨y, hy⟩ := hc
          have z'' := (right_1 a).1 y hy
          simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, true_and]
        . simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, Finset.mem_coe]
          simp [← Finset.mem_coe, (Set.ext_iff.mp w_Dom.symm) a] at hc
          apply Iff.intro
          · intro a_1
            exact False.elim (hc v a_1)
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            exact False.elim (hc w h)


      · have z := (ih₂ w₂ hw₂)
        have w_Dom : w₂.Dom = q₂.schema dbi.schema := by
          exact RA.Query.evaluate.validSchema q₂ right w₂ hw₂
        have z' : w₂.Dom ⊆ t.Dom := by simp_all
        apply FOL.BoundedQuery.Realize.tuple_restrict (ra_to_fol_query.isWellTyped q₂ dbi.schema right) z.1 z'

        ext a v
        simp [PFun.mem_restrict]
        by_cases hc : a ∈ w₂.Dom
        . simp [PFun.mem_dom] at hc
          have ⟨y, hy⟩ := hc
          have z'' := (right_1 a).2.1 y hy
          simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, true_and]
        . simp_all only [Finset.coe_union, subset_refl, and_self, Set.subset_union_left, Finset.mem_coe]
          simp [← Finset.mem_coe, (Set.ext_iff.mp w_Dom.symm) a] at hc
          apply Iff.intro
          · intro a_1
            exact False.elim (hc v a_1)
          · intro a_1
            obtain ⟨left_1, right_2⟩ := a_1
            obtain ⟨w, h⟩ := left_1
            exact False.elim (hc w h)

    | r f sq ih =>
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.r f sq) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.r f sq) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        RA.Query.isWellTyped.r_def, RA.Query.evaluateT.r_def, renameT, exists_eq_right',
        Set.mem_setOf_eq, forall_const, and_self, implies_true]
      obtain ⟨left, right⟩ := h
      sorry

theorem ra_to_fol_evalT.mem (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema):
  ∀t, t ∈ raQ.evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    intro t
    apply Iff.intro
    . exact ra_to_fol_evalT.rf h_ra_wt t
    . exact ra_to_fol_evalT.fr h_ra_wt t

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


theorem fol_to_ra {dbi} [FOL.folStruc dbi] (folQ : FOL.Query) (h : folQ.isWellTyped dbi.schema) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
