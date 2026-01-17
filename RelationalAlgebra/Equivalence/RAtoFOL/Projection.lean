import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {rs q} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Inhabited μ]

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Projection operation. -/
theorem toFOL_evalT.p_def_eq (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih: (toFOL dbi.schema q).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (toFOL dbi.schema (.p rs q)).evaluateT dbi = RA.Query.evaluateT dbi (.p rs q) := by
      simp at h
      obtain ⟨left, right⟩ := h
      simp only [FOL.Query.evaluateT, toFOL, FOL.Query.RealizeMin.and_def]
      rw [← toFOL_schema left] at right
      rw [projectQuery.schema_def (toFOL dbi.schema q) rs right]
      simp only [RA.Query.evaluateT, projectionT]
      ext t
      simp_all only [Set.mem_setOf_eq]

      apply Iff.intro
      · intro a
        obtain ⟨h, right_1⟩ := a
        have ⟨dropSet, h_dropSet⟩ : ∃s, (FOL.BoundedQuery.schema (toFOL dbi.schema q) \ rs) = s := by simp
        simp_all only [projectQuery.def, Nat.add_zero, forall_true_left]
        rw [FOL.BoundedQuery.Realize.exs_def] at right_1
        obtain ⟨w, hw⟩ := right_1
        unfold projectAttribute at hw
        rw [← ih]
        simp only [FOL.Query.evaluateT.def, FOL.Query.RealizeMin.and_def]
        have : ∀a' ∈ dropSet, a' ∈ FOL.BoundedQuery.schema (toFOL dbi.schema q) \ rs := by
          intro a_1 a_2
          rw [h_dropSet]
          exact a_2
        use (Sum.elim t (PFun.lift w) ∘ fun a' ↦ if h : a' ∈ dropSet then Sum.inr (RM.RelationSchema.index (this a' h)) else Sum.inl a')
        simp_all [Function.comp_apply]
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
                simp_all only [implies_true, Sum.elim_inl]
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
            rw [← FOL.BoundedQuery.Realize] at hw
            convert hw
            ext a
            by_cases hc : a ∈ dropSet
            . subst h_dropSet
              simp_all only [Finset.mem_sdiff, FOL.TupleToFun, Function.comp_apply, not_false_eq_true,
                and_self, ↓reduceDIte, Sum.elim_inr, PFun.coe_val, Part.getOrElse_some]
            . simp [hc]
              congr
              simp [hc]
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
            simp_all only [implies_true, Sum.elim_inl, true_and]
            intro a_2
            apply Part.eq_none_iff'.mpr
            rw [Part.dom_iff_mem, ← PFun.mem_dom, h]
            exact a_2

      . intro a
        simp_all only [projectQuery.def, Nat.add_zero, FOL.BoundedQuery.Realize.exs_def]
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        apply And.intro
        · ext a
          simp_all only [PFun.mem_dom, Finset.mem_coe]
          have h1 := RA.Query.evaluate.validSchema q left w left_1
          have h2 := (toFOL_schema left).symm
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
          use λ i => (w (RM.RelationSchema.fromIndex i)).get (by
            rw [@Part.dom_iff_mem, ← PFun.mem_dom, w_dom]
            have := RM.RelationSchema.fromIndex_mem i
            simp_all [toFOL_schema]
          )
          rw [← ih] at left_1
          simp at left_1
          simp_all
          convert left_1.2
          ext a
          simp_all
          by_cases hc : a ∈ rs
          . simp_all only [Finset.mem_sdiff, not_true_eq_false, and_false,
              not_false_eq_true, projectAttribute_not_mem, Sum.elim_inl]
            rw [← FOL.TupleToFun]
            exact FOL.TupleToFun.tuple_eq_att_ext ((right_1 a).1 hc)
          . unfold projectAttribute
            simp_all [Finset.mem_sdiff, not_false_eq_true, and_true]
            by_cases hc' : (w a).Dom
            all_goals
            . have := by rw [@Part.dom_iff_mem, ← PFun.mem_dom, w_dom] at hc'; exact hc';
              simp_all [Part.getOrElse, toFOL_schema left]
