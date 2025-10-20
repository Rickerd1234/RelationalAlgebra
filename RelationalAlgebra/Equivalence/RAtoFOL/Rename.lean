import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi f q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.r_def.mp (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: ∀t, (ra_to_fol_query q dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.r f q) dbi.schema).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.r f q) := by
      simp only [RA.Query.isWellTyped, ra_to_fol_query, FOL.Query.RealizeMin.and_def,
        FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
        CompTriple.comp_eq, Fin.natAdd_zero, FOL.BoundedQuery.relabel_schema, Function.comp_apply,
        Sum.getLeft?_inl, Part.coe_some, Finset.pimage_some, Finset.coe_image,
        RA.Query.evaluateT, renameT, exists_eq_right', Set.mem_setOf_eq, and_imp] at ⊢ h
      intro t h_dom h_rel
      apply ih
      . simp_all [FOL.Query.RealizeMin.and_def]
        apply And.intro
        . ext a
          rw [Set.ext_iff] at h_dom
          simp_all only [PFun.mem_dom, Set.mem_image, Finset.mem_coe, Function.comp_apply]
          obtain ⟨left, right⟩ := h
          simp_all only [implies_true]
          rw [← PFun.mem_dom, h_dom]
          simp_all
          apply Iff.intro
          · intro a_1
            obtain ⟨w, h⟩ := a_1
            obtain ⟨left_1, right_1⟩ := h
            convert left_1
            simp [right.1 right_1]
          · intro a_1
            use a
        . intro h_1
          simp_all only
          obtain ⟨left, right⟩ := h
          convert h_rel
          ext a
          unfold FOL.TupleToFun
          simp_all only [Function.comp_apply, Sum.elim_inl]
          by_cases hc : (t (f a)).Dom
          . simp_all [Part.getOrElse_of_dom]
          . simp_all [Part.getOrElse_of_not_dom]

theorem ra_to_fol_evalT.r_def.mpr (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.r f q) → (ra_to_fol_query (.r f q) dbi.schema).RealizeMin dbi t := by
      intro t h_RA_eval
      rw [FOL.Query.RealizeMin.and_def]
      apply And.intro (by simp_all [RA.Query.evaluate.validSchema (.r f q) h t h_RA_eval, ra_to_fol_query_schema])

      simp only [ra_to_fol_query]
      simp_all only [ra_to_fol_query_schema, FOL.Query.RealizeMin.and_def,
        RA.Query.isWellTyped, RA.Query.evaluateT, renameT, exists_eq_right',
        Set.mem_setOf_eq, forall_const, and_self, implies_true]
      obtain ⟨left, right⟩ := h
      simp_all only [FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero,
        Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq, Fin.natAdd_zero]
      intro h_1
      simp_all only [Pi.default_def, Nat.default_eq_zero]
      convert (ih (Sum.elim t (default : (Fin 0 →. RM.Value)) ∘ Sum.inl ∘ f) h_RA_eval).2 ?_
      . unfold FOL.TupleToFun
        ext a
        simp_all only [Function.comp_apply, Sum.elim_inl]
        by_cases hc : (t (f a)).Dom
        . simp_all [Part.getOrElse_of_dom]
        . simp_all [Part.getOrElse_of_not_dom]
      . exact RA.Query.evaluate.validSchema q left (Sum.elim t default ∘ Sum.inl ∘ f) h_RA_eval

theorem ra_to_fol_evalT.r_def_eq (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: (ra_to_fol_query q dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (ra_to_fol_query (.r f q) dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi (.r f q) := by
      ext t
      apply Iff.intro
      . exact ra_to_fol_evalT.r_def.mp h
          (λ t' => ((Set.ext_iff.mp ih) t').mp)
          t
      . exact ra_to_fol_evalT.r_def.mpr h
          (λ t' => ((Set.ext_iff.mp ih) t').mpr)
          t
