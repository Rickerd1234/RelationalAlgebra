import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rs q} [FOL.folStruc dbi]

theorem ra_to_fol_evalT.p_def_eq (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih: (ra_to_fol_query q dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (ra_to_fol_query (.p rs q) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.p rs q) := by
      simp at h
      obtain ⟨left, right⟩ := h
      simp only [FOL.Query.evaluateT, ra_to_fol_query, FOL.Query.RealizeMin]
      rw [← ra_to_fol_query_schema left] at right
      rw [projectQuery.schema_def (ra_to_fol_query q dbi.schema) rs right]
      simp only [RA.Query.evaluateT.p_def, projectionT]
      ext t
      simp_all only [Set.mem_setOf_eq]

      apply Iff.intro
      · intro a
        obtain ⟨h, right_1⟩ := a
        have ⟨dropSet, h_dropSet⟩ : ∃s, (FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) \ rs) = s := by simp
        induction dropSet using Finset.induction_on with
        | empty =>
          have : rs = FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) := by
            refine Finset.Subset.antisymm right (Finset.sdiff_eq_empty_iff_subset.mp h_dropSet)

          rw [this, projectQuery.q_schema_def] at h
          rw [← ih]
          simp
          use t
          simp_all only [subset_refl, FOL.BoundedQuery.Realize.def, sdiff_self, Finset.bot_eq_empty,
            and_self, implies_true, true_and]
          intro a a_1
          apply Part.eq_none_iff'.mpr fun a ↦ a_1 (right_1 a)
        | insert h' ih =>
          rename_i a ds
          simp_all only [projectQuery.def, Nat.add_zero, Finset.insert_eq_self,
            not_isEmpty_of_nonempty, IsEmpty.forall_iff, and_true, IsEmpty.exists_iff]
          simp at h
          obtain ⟨w, h⟩ := h
          unfold projectAttribute at h
          simp [h_dropSet] at h
          rw [← ih]
          simp
          have : ∀a' ∈ insert a ds, a' ∈ FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) \ rs := by
            intro a_1 a_2
            rw [h_dropSet]
            exact a_2
          use (Sum.elim t w ∘ fun a' ↦ if h : a' = a ∨ a' ∈ ds then Sum.inr (RM.RelationSchema.index (this a' (by simp_all))) else Sum.inl a')
          simp_all only [ra_to_fol_query.isWellTyped, dite_eq_ite, Function.comp_apply]
          apply And.intro
          · apply And.intro
            · apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp h
              . ext a v
                exact Fin.elim0 a
              . rfl
            · rw [Set.subset_def]
              intro x a_1
              simp_all only [ra_to_fol_query.isWellTyped, PFun.mem_dom, Function.comp_apply, Finset.mem_coe]
              obtain ⟨w_1, h_1⟩ := a_1
              split at h_1
              next h_2 =>
                simp_all only [ra_to_fol_query.isWellTyped, Sum.elim_inr]
                have := this x (by simp [h_2])
                simp at this
                exact this.1
              next
                h_2 =>
                simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_insert, or_false, not_or, Sum.elim_inl]
                obtain ⟨left_1, right_2⟩ := h_2
                simp_all only [ra_to_fol_query.isWellTyped, implies_true]
                apply right
                apply right_1
                simp_all only [ra_to_fol_query.isWellTyped, PFun.mem_dom]
                apply Exists.intro
                · exact h_1
          · intro a_1
            split
            next h_1 =>
              simp_all only [ra_to_fol_query.isWellTyped, Sum.elim_inr]
              cases h_1 with
              | inl h_2 =>
                subst h_2
                apply And.intro
                · intro a
                  by_contra hc
                  simp at this
                  exact this.1.2 a
                · intro a
                  simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_insert, or_false]
                  exact Part.eq_none_iff'.mpr fun a_2 ↦ a (right_1 a_2)
              | inr h_3 =>
                apply And.intro
                · intro a_2
                  have : a_1 ∈ FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) \ rs := by simp_all
                  by_contra hc
                  simp at this
                  exact this.2 a_2
                · intro a_2
                  simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_insert, or_false]
                  apply Part.eq_none_iff'.mpr fun a ↦ a_2 (right_1 a)
            next
              h_1 =>
              simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_insert, or_false, not_or, Sum.elim_inl,
                implies_true, true_and]
              intro a_2
              obtain ⟨left_1, right_2⟩ := h_1
              apply Part.eq_none_iff'.mpr fun a ↦ a_2 (right_1 a)
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        apply And.intro
        · simp only [projectQuery.def, Nat.add_zero, FOL.BoundedQuery.Realize.exs_def,
          FOL.BoundedQuery.Realize.relabel_def, Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq]
          use λ i => w (RM.RelationSchema.fromIndex i)
          rw [← ih] at left_1
          simp at left_1
          apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp left_1.1
          . ext a v
            exact Fin.elim0 a
          . obtain ⟨left_1, right_2⟩ := left_1
            ext a v
            simp_all only [ra_to_fol_query.isWellTyped, Function.comp_apply]
            by_cases a ∈ rs
            . simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_sdiff, not_true_eq_false, and_false,
                not_false_eq_true, projectAttribute_not_mem, Sum.elim_inl]
            . unfold projectAttribute
              simp_all
              apply Iff.intro
              · intro a_1
                split
                next h_1 =>
                  simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_sdiff, not_false_eq_true, and_self,
                    Sum.elim_inr, RM.RelationSchema.fromIndex_index_eq]
                next
                  h_1 =>
                  have : w.Dom ⊆ FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) := by simp_all
                  simp_all only [ra_to_fol_query.isWellTyped, Sum.elim_inl, not_false_eq_true, Part.not_mem_none]
                  apply h_1
                  apply this
                  simp_all
                  exact Exists.intro v a_1
              · intro a_1
                split at a_1
                next h_1 =>
                  simp_all only [ra_to_fol_query.isWellTyped, Finset.mem_sdiff, not_false_eq_true, and_self,
                    Sum.elim_inr, RM.RelationSchema.fromIndex_index_eq]
                next h_1 =>
                  simp_all only [ra_to_fol_query.isWellTyped, Sum.elim_inl, not_false_eq_true, Part.not_mem_none]
        · rw [Set.subset_def]
          intro x a
          simp_all only [PFun.mem_dom, Finset.mem_coe]
          obtain ⟨w_1, h⟩ := a
          by_contra hc
          simp_all only [not_false_eq_true, Part.not_mem_none]
