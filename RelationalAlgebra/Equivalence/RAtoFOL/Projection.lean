import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi rs q} [FOL.folStruc dbi]

theorem ra_to_fol_evalT.p_def.mp (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih: RA.Query.isWellTyped dbi.schema q → ∀t, (ra_to_fol_query q dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.p rs q) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.p rs q) := by
      intro t
      simp only [RA.Query.isWellTyped.p_def, ra_to_fol_query, projectQuery.def, Nat.add_zero,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.schema.exs_def, FOL.BoundedQuery.relabel_schema,
        Finset.coe_pimage, RA.Query.evaluateT.p_def, projectionT, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_2 a_3
      obtain ⟨left, right⟩ := h
      have h_t_dom := by exact FOL.BoundedQuery.Realize.schema_sub_Dom a_2
      simp [projectAttribute, *] at h_t_dom
      have h_rs : ↑rs ⊆ t.Dom := by
        rw [Set.subset_def]
        intro x hx
        simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped,
          ra_to_fol_query_schema, and_imp, forall_const, true_and, dite_not, Part.dom_iff_mem,
          Finset.mem_coe, PFun.mem_dom]
        exact h_t_dom x x (right hx) (by simp [hx])
      use t.restrict h_rs
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        and_imp, forall_const, projectAttribute, Finset.mem_sdiff, true_and, dite_not]
      apply And.intro
      · apply ih
        . have ⟨dropSet, h_dropSet⟩ : ∃s, (FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema) \ rs) = s := by simp
          induction dropSet using Finset.induction_on with
          | empty =>
            rw [h_dropSet] at a_2
            unfold projectAttribute at a_2
            simp at a_2
            have z : rs = q.schema dbi.schema := by simp_all; exact Finset.Subset.antisymm right h_dropSet
            have h_rs' : ↑(FOL.BoundedQuery.schema (ra_to_fol_query q dbi.schema)) ⊆ PFun.Dom t := by simp_all
            have z' := FOL.BoundedQuery.Realize.tuple_restrict2
              (ra_to_fol_query.isWellTyped q dbi.schema left)
              (h_rs')
              a_2
            have : (PFun.restrict t h_rs) = (PFun.restrict t h_rs') := by aesop
            simp [this, z']
          | insert h ih =>
            rename_i a ds
            sorry
        . exact right
      · intro a
        apply And.intro
        · intro a_1
          ext v : 1
          simp_all only [ra_to_fol_query.isWellTyped, PFun.mem_restrict, Finset.mem_coe, true_and]
        · intro a_1
          rw [Set.subset_def] at a_3
          by_contra hc
          simp [Part.ne_none_iff, Part.eq_some_iff, ← PFun.mem_dom] at hc
          have h_image := a_3 a hc
          simp [PFun.mem_image] at h_image
          have ⟨a', ha', ha''⟩ := h_image
          simp_all
          by_cases hc' : a' ∈ rs
          . simp_all
          . simp_all

theorem ra_to_fol_evalT.p_def.mpr (h : RA.Query.isWellTyped dbi.schema (.p rs q))
  (ih : RA.Query.isWellTyped dbi.schema q → ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeDom dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.p rs q) → (ra_to_fol_query (.p rs q) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      have t_Dom : t.Dom = rs := by
        exact RA.Query.evaluate.validSchema (.p rs q) h t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.p rs q) dbi.schema)
          (by simp_all)

      simp only [ra_to_fol_query]
      have : t = t.restrict (Set.Subset.antisymm_iff.mp t_Dom.symm).1 := by simp_all
      rw [this]
      apply projectQuery.Realize_restrict_def
      . simp at h
        obtain ⟨left, right⟩ := h
        exact ra_to_fol_query.isWellTyped q dbi.schema left
      . simp_all [projectionT]
        obtain ⟨left, right⟩ := h
        obtain ⟨w, h⟩ := h_RA_eval
        obtain ⟨left_1, right_1⟩ := h

        have : t = w := by
          ext a v
          by_cases a ∈ rs
          . aesop
          . sorry
            -- ???
        rw [this]
        exact (ih w left_1).1
