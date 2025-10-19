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
        simp_all only [projectQuery.def, Nat.add_zero, forall_true_left]
        have := FOL.dec_dom h
        simp only [FOL.TupleToFun.def] at right_1
        rw [FOL.BoundedQuery.Realize.exs_def] at right_1
        obtain ⟨w, hw⟩ := right_1
        unfold projectAttribute at hw
        rw [← ih]
        simp
        have : ∀a' ∈ dropSet, a' ∈ FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) \ rs := by
          intro a_1 a_2
          rw [h_dropSet]
          exact a_2
        use (Sum.elim t (PFun.lift w) ∘ fun a' ↦ if h : a' ∈ dropSet then Sum.inr (RM.RelationSchema.index (this a' (by simp_all))) else Sum.inl a')
        simp_all [dite_eq_ite, Function.comp_apply]
        apply And.intro
        · apply And.intro
          · ext a'
            simp_all only [PFun.mem_dom, Function.comp_apply, Finset.mem_coe]
            apply Iff.intro
            · intro a_2
              obtain ⟨w_1, h_1⟩ := a_2
              split at h_1
              next h_2 =>
                simp_all only [Sum.elim_inr]
                subst h_dropSet
                simp_all
                have := this a' h_2
                rw [Finset.mem_sdiff] at this
                exact this.1
              next h_2 =>
                simp_all only [Finset.mem_insert, implies_true, not_or, Sum.elim_inl]
                rw [Set.ext_iff] at h
                by_contra hc
                have := (h a').1 (by refine (PFun.mem_dom t a').mpr (Exists.intro w_1 h_1))
                exact hc (right this)
            · intro a_2
              split
              next h_1 =>
                simp_all only [Sum.elim_inr, PFun.coe_val, Part.mem_some_iff, exists_eq]

              next h_1 =>
                simp [← h_dropSet, Finset.mem_sdiff, a_2] at h_1
                rw [Set.ext_iff] at h
                simp [← PFun.mem_dom]
                exact (h a').mpr h_1
          · intro h'
            apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp hw
            . ext a
              exact Fin.elim0 a
            . have := FOL.dec_dom h'
              simp [FOL.TupleToFun.def h']
              ext a
              simp
              by_cases a ∈ dropSet
              . simp_all only [Finset.mem_sdiff, not_false_eq_true, and_self, ↓reduceDIte, Sum.elim_inr, PFun.coe_val,
                  Part.getOrElse_some]
              . simp_all only [dite_false, Sum.elim_inl]
        · intro a_1
          split
          next h_1 =>
            simp_all only [Sum.elim_inr]
            subst h_dropSet
            simp_all
            apply And.intro
            · intro h_2
              by_contra hc
              simp at h_1
              exact h_1.2 h_2
            · intro a
              simp_all only [Finset.mem_sdiff, not_false_eq_true, and_self, implies_true, and_true]
              apply Part.eq_none_iff'.mpr
              rw [Part.dom_iff_mem, ← PFun.mem_dom, h]
              exact a
          next h_1 =>
            simp_all only [Finset.mem_insert, implies_true, not_or, Sum.elim_inl, true_and]
            intro a_2
            apply Part.eq_none_iff'.mpr
            rw [Part.dom_iff_mem, ← PFun.mem_dom, h]
            exact a_2

      . intro a
        simp_all only [projectQuery.def, Nat.add_zero, FOL.BoundedQuery.Realize.exs_def,
          FOL.BoundedQuery.Realize.relabel_def, Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq]
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        apply And.intro
        · ext a
          simp_all only [PFun.mem_dom, Finset.mem_coe]
          have h1 := RA.Query.evaluate.validSchema q left w left_1
          have h2 := (ra_to_fol_query_schema left).symm
          apply Iff.intro
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            by_contra hc
            have := (right_1 a).2 hc
            simp [Part.eq_none_iff] at this
            exact this w_1 h
          · intro a_1
            simp_all only
            rw [← @PFun.mem_dom, h1]
            exact right a_1
        · intro h'
          have w_dom : w.Dom  = q.schema dbi.schema := RA.Query.evaluate.validSchema q left w left_1
          have := FOL.dec_dom h'
          have := FOL.dec_dom w_dom
          use λ i => (w (RM.RelationSchema.fromIndex i)).get (by
            rw [@Part.dom_iff_mem, ← PFun.mem_dom, w_dom]
            have := RM.RelationSchema.fromIndex_mem i
            simp_all [ra_to_fol_query_schema]
          )
          rw [← ih] at left_1
          simp at left_1
          apply (FOL.BoundedQuery.Realize.assignment_eq_ext ?_ ?_).mp (left_1.2 left_1.1)
          . ext a
            exact Fin.elim0 a
          . obtain ⟨left_1, right_2⟩ := left_1
            ext a
            simp_all [Function.comp_apply]
            by_cases a ∈ rs
            . simp_all only [FOL.TupleToFun.def, Finset.mem_sdiff, not_true_eq_false, and_false,
                not_false_eq_true, projectAttribute_not_mem, Sum.elim_inl]
            . unfold projectAttribute
              by_cases hc : (w a).Dom
              all_goals
              . have := by rw [@Part.dom_iff_mem, ← PFun.mem_dom, w_dom] at hc; exact hc;
                simp_all [Part.getOrElse]
