import RelationalAlgebra.Equivalence.RAtoFOL.Defs

open RM

@[simp]
theorem ra_to_fol_evalT.FOL_evaluateT [struc : FOL.folStruc] (dbi : DatabaseInstance) (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  t ∈ (ra_to_fol_query raQ dbi.schema).evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    simp_all only [FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.RealizeValidDom.def,
      IsEmpty.forall_iff, DatabaseInstance.default_ran_sub_domain, and_self, and_true, FOL.Query.evaluateT]
    simp_all
    apply Iff.intro
    · intro a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨w_1, h_1⟩ := h_1
      obtain ⟨left, right⟩ := w_1
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      subst h_1
      apply And.intro
      · apply And.intro
        · have z : PFun.restrict w (FOL.Query.RealizeDom.schema_sub_Dom (ra_to_fol_query raQ dbi.schema) (by simp_all; exact right_1)) = w := by aesop
          simp_all [z]
        · apply And.intro
          · intro a a_1
            simp [PFun.Dom, Part.dom_iff_mem] at right
            simp_all [Set.subset_def]
            apply Part.dom_iff_mem.mpr
            use (w a).get (left_1 a a_1)
            simp_all [Part.get_mem]
          · intro v h
            rw [PFun.ran] at *
            simp [PFun.Dom, Part.dom_iff_mem] at right
            simp_all [Set.subset_def]
            aesop
      · simp_all [PFun.restrict, PFun.Dom, Part.restrict]
    · intro a
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      use t
      simp_all
      aesop

theorem ra_to_fol_evalT.mem [struc : FOL.folStruc] (dbi : DatabaseInstance) (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema):
  ∀t, t ∈ raQ.evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    sorry
--     have h_fol_wt := ra_to_fol_query.isWellTyped raQ dbi.schema h_ra_wt
--     have h_schema_eq := (ra_to_fol_query_schema raQ dbi.schema h_ra_wt (h_fol_wt)).symm

--     induction raQ with
--     | R rn =>
--       simp only [ra_to_fol_query]
--       simp_all only [RA.Query.isWellTyped.R_def, ra_to_fol_query.isWellTyped, RA.Query.schema_R,
--         RA.Query.evaluateT.R_def, FOL.Query.RealizeDom.def,
--         FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.Realize.R_def, Function.comp_apply,
--         FOL.Term.realizeSome.def, FOL.BoundedQuery.toFormula_rel, FirstOrder.Language.BoundedFormula.realize_rel,
--         FOL.folStruc_apply_RelMap, FOL.BoundedQuery.RealizeValidDom.def,
--         Set.mem_toFinset, Set.mem_setOf_eq, forall_exists_index, IsEmpty.forall_iff, true_and, Set.coe_toFinset]
--       simp_all only [FOL.outVar.def, FirstOrder.Language.Term.realize_var, Sum.elim_inl,
--         FirstOrder.Language.Term.varFinsetLeft.eq_1, Finset.mem_singleton]
--       intro t
--       apply Iff.intro
--       · intro ht
--         simp_all only [RelationSchema.fromIndex_Dom, implies_true, true_and]
--         apply And.intro
--         · apply And.intro
--           · rw [FOL.ArityToTuple.def_fromIndex t]
--             . exact ht
--             . simp [(dbi.relations rn).validSchema t ht]
--           · apply And.intro
--             . intro a ha
--               simp at ha
--               rw [← DatabaseInstance.validSchema_def rn] at ha
--               exact (RelationInstance.validSchema.iff_def ht).mp ha
--             . apply And.intro
--               · exact DatabaseInstance.t_ran_sub_domain ht
--               · exact DatabaseInstance.default_ran_sub_domain
--         · simp [(dbi.relations rn).validSchema t ht]
--       · intro a
--         obtain ⟨left, right⟩ := a
--         obtain ⟨left, right_1⟩ := left
--         obtain ⟨left, right_2⟩ := left
--         obtain ⟨left_1, right_1⟩ := right_1
--         obtain ⟨left_2, right_1⟩ := right_1
--         rw [FOL.ArityToTuple.def_fromIndex] at right_2
--         . exact right_2
--         . simp at right
--           apply Set.Subset.antisymm right
--           intro a ha
--           simp_all [Part.dom_iff_mem]


--     | s a b p q q_ih =>
--       simp only [ra_to_fol_query]
--       simp only [RA.Query.evaluateT.s_def, FOL.outVar.def, FOL.Query.RealizeDom.def,
--         FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.Realize.tEq_def, FOL.Term.realizeSome.def,
--         FirstOrder.Language.Term.realize_var, Sum.elim_inl, FOL.BoundedQuery.RealizeValidDom.def,
--         FOL.BoundedQuery.schema.tEq_def, IsEmpty.forall_iff,
--         DatabaseInstance.default_ran_sub_domain, and_self, and_true]
--       intro t
--       apply Iff.intro
--       · intro a_1
--         apply And.intro
--         · apply And.intro
--           · apply And.intro
--             · sorry
--             · apply And.intro
--               · sorry
--               · apply And.intro
--                 · sorry
--                 · simp [FirstOrder.Language.BoundedFormula.Realize, selectionT] at a_1 ⊢
--                   exact a_1.2
--           · apply And.intro
--             · intro a_2 a_3
--               simp_all only [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
--                 FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
--                 FOL.BoundedQuery.RealizeValidDom.def, IsEmpty.forall_iff,
--                 DatabaseInstance.default_ran_sub_domain, and_self, and_true, forall_const,
--                 RA.Query.isWellTyped.s_def, RA.Query.schema_s, implies_true]
--               sorry
--             · simp [selectionT] at a_1
--               sorry
--         · sorry
--       · intro a_1
--         obtain ⟨left, right⟩ := a_1
--         obtain ⟨left, right_1⟩ := left
--         obtain ⟨left, right_2⟩ := left
--         obtain ⟨left_1, right_1⟩ := right_1
--         obtain ⟨left_2, right_2⟩ := right_2
--         obtain ⟨left_3, right_2⟩ := right_2
--         simp [selectionT]
--         apply And.intro
--         . rw [q_ih]
--           . simp_all
--           . simp_all
--           . simp_all
--           . simp_all [ra_to_fol_query]
--         . exact right_2

--     | j q₁ q₂ q₁_ih q₂_ih =>
--       simp only [ra_to_fol_query]
--       simp only [RA.Query.evaluateT.j_def, FOL.Query.RealizeDom.def,
--         FOL.BoundedQuery.RealizeDom.def, FOL.BoundedQuery.Realize.and_def,
--         FOL.BoundedQuery.RealizeValidDom.def, FOL.BoundedQuery.schema.and_def, Finset.mem_union,
--         IsEmpty.forall_iff, DatabaseInstance.default_ran_sub_domain, and_self, and_true,
--         Finset.coe_union]
--       obtain ⟨left, right⟩ := h_ra_wt
--       intro t
--       apply Iff.intro
--       · intro a
--         apply And.intro
--         · apply And.intro
--           · apply And.intro
--             · simp [joinT] at a
--               sorry
--             · simp [joinT] at a
--               sorry
--           · apply And.intro
--             · intro a_1 a_2
--               simp_all only [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
--                 FOL.Query.RealizeDom.def, FOL.BoundedQuery.RealizeDom.def,
--                 FOL.BoundedQuery.RealizeValidDom.def, IsEmpty.forall_iff,
--                 DatabaseInstance.default_ran_sub_domain, and_self, and_true, forall_const,
--                 RA.Query.isWellTyped.j_def, RA.Query.schema_j, FOL.BoundedQuery.schema.and_def,
--                 Finset.mem_union]
--               cases a_2 with
--               | inl h => sorry
--               | inr h_1 => sorry
--             · sorry
--         · sorry
--       · intro a
--         obtain ⟨left_1, right_1⟩ := a
--         obtain ⟨left_1, right_2⟩ := left_1
--         obtain ⟨left_1, right_3⟩ := left_1
--         obtain ⟨left_2, right_2⟩ := right_2
--         simp [joinT]
--         use t
--         sorry
--         -- rw [q₁_ih]
--         -- . apply And.intro
--         --   . sorry
--         --   . use t
--         --     rw [q₂_ih]
--         --     . sorry
--         --     . sorry
--         --     . simp_all [ra_to_fol_query]
--         --     . simp_all
--         -- . simp_all
--         -- . simp_all
--         -- . simp_all

--     | _ => sorry

theorem ra_to_fol_eval [struc : FOL.folStruc] {dbi} (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema) :
  raQ.evaluate dbi h_ra_wt = (ra_to_fol_query raQ dbi.schema).evaluate dbi := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    simp_all [ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, true_and]
    ext t
    simp_all only [ra_to_fol_evalT.FOL_evaluateT]
    exact ra_to_fol_evalT.mem dbi raQ h_ra_wt t

theorem ra_to_fol [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.Query, raQ.evaluate dbi h = folQ.evaluate dbi := by
    use ra_to_fol_query raQ dbi.schema
    exact ra_to_fol_eval raQ h


theorem fol_to_ra [FOL.folStruc] {dbi} (folQ : FOL.Query) (h : folQ.isWellTyped) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
