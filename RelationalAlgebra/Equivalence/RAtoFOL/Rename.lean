import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {dbi f q} [struc : FOL.folStruc dbi]

theorem ra_to_fol_evalT.r_def.mp (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: ∀t, (ra_to_fol_query q dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (ra_to_fol_query (.r f q) dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi (.r f q) := by
      simp only [RA.Query.isWellTyped.r_def, ra_to_fol_query, FOL.Query.RealizeDom.def,
        FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
        CompTriple.comp_eq, Fin.natAdd_zero, FOL.BoundedQuery.relabel_schema, Function.comp_apply,
        Sum.getLeft?_inl, Part.coe_some, Finset.pimage_some, Finset.coe_image,
        RA.Query.evaluateT.r_def, renameT, exists_eq_right', Set.mem_setOf_eq, and_imp] at ⊢ h
      intro t a h_dom
      apply ih
      . simp_all
        apply And.intro
        . exact a
        . simp [Set.subset_def] at h_dom ⊢
          intro x x_1 h_1
          obtain ⟨left, right⟩ := h
          have ⟨x', hx', hx''⟩ := h_dom (f x) x_1 h_1
          simp_all [right.1 hx'']

theorem ra_to_fol_evalT.r_def.mpr (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (ra_to_fol_query q dbi.schema).RealizeDom dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.r f q) → (ra_to_fol_query (.r f q) dbi.schema).RealizeDom dbi t := by
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.r f q) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.r f q) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        RA.Query.isWellTyped.r_def, RA.Query.evaluateT.r_def, renameT, exists_eq_right',
        Set.mem_setOf_eq, forall_const, and_self, implies_true]
      obtain ⟨left, right⟩ := h
      simp_all only [ra_to_fol_query.isWellTyped, FOL.BoundedQuery.Realize.relabel_def, Nat.add_zero,
        Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq, Fin.natAdd_zero]
      exact (ih (Sum.elim t (default : (Fin 0 →. RM.Value)) ∘ Sum.inl ∘ f) h_RA_eval).1

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
