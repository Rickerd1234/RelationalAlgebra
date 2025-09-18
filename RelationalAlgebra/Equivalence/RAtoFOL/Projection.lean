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
        simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
          forall_const, true_and, dite_not, Finset.mem_coe, PFun.mem_dom, Part.dom_iff_mem]
        exact h_t_dom x x (right hx) (by simp [hx])
      use t.restrict h_rs
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        and_imp, forall_const, projectAttribute, Finset.mem_sdiff, true_and, dite_not]
      apply And.intro
      · apply ih
        . simp_all only [ra_to_fol_query.isWellTyped, FOL.BoundedQuery.Realize.exs_def,
          FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
          CompTriple.comp_eq]
          obtain ⟨w, h⟩ := a_2
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
      simp_all only [RA.Query.isWellTyped.p_def, RA.Query.evaluateT.p_def, projectionT,
        Set.mem_setOf_eq, forall_const]
      simp_all only [projectQuery.def, Nat.add_zero]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := h_RA_eval
      obtain ⟨hw, right_1⟩ := h

      have z := (ih w hw)
      have w_Dom : w.Dom = q.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema q left w hw

      simp_all only [ra_to_fol_query.isWellTyped, subset_refl, and_self,
        FOL.BoundedQuery.Realize.exs_def, FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero,
        Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq]
      sorry
