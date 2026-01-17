import RelationalAlgebra.Equivalence.RAtoFOL.Conversion

variable {f q} {dbi : RM.DatabaseInstance ρ α μ} [LinearOrder α] [struc : FOL.folStruc dbi] [Inhabited μ]

/-- One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Rename operation. -/
theorem toFOL.evalT_def.r_def.mp (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: ∀t, (toFOL dbi.schema q).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi q) :
    ∀t, (toFOL dbi.schema (.r f q)).RealizeMin dbi t → t ∈ RA.Query.evaluateT dbi (.r f q) := by
      simp only [RA.Query.isWellTyped, toFOL, FOL.Query.RealizeMin.and_def,
        FOL.BoundedQuery.relabel_schema, Function.comp_apply, Sum.getLeft?_inl, Part.coe_some,
        Finset.pimage_some, Finset.coe_image, RA.Query.evaluateT, renameT,
        Set.mem_setOf_eq, and_imp] at ⊢ h
      intro t h_dom h_rel
      apply ih
      . simp_all only [FOL.Query.RealizeMin.and_def, and_imp, forall_true_left,
        FOL.BoundedQuery.Realize.relabel_formula, Nat.add_zero,
        FirstOrder.Language.BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
        Function.comp_id, Fin.natAdd_zero]
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

/-- (Reverse) One-sided proof for the tuple evaluation equivalence of the RA to FOL conversion for the Rename operation. -/
theorem toFOL.evalT_def.r_def.mpr (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih : ∀t ∈ RA.Query.evaluateT dbi q, (toFOL dbi.schema q).RealizeMin dbi t) :
    ∀t, t ∈ RA.Query.evaluateT dbi (.r f q) → (toFOL dbi.schema (.r f q)).RealizeMin dbi t := by
      intro t h_RA_eval
      rw [FOL.Query.RealizeMin.and_def]
      apply And.intro (by simp_all only [RA.Query.evaluate.validSchema (.r f q) h t h_RA_eval, toFOL.schema_def])

      simp only [toFOL]
      simp_all only [toFOL.schema_def, FOL.Query.RealizeMin.and_def, RA.Query.isWellTyped,
        RA.Query.evaluateT, renameT, Set.mem_setOf_eq]
      obtain ⟨left, right⟩ := h
      simp_all only [FOL.BoundedQuery.Realize.relabel_formula,
        Nat.add_zero, FirstOrder.Language.BoundedFormula.realize_relabel, Fin.castAdd_zero,
        Fin.cast_refl, Fin.natAdd_zero]
      intro h_1
      convert (ih (Sum.elim t (default : (Fin 0 →. μ)) ∘ Sum.inl ∘ f) h_RA_eval).2 ?_
      . unfold FOL.TupleToFun
        ext a
        simp_all only [Function.comp_apply, Sum.elim_inl]
        by_cases hc : (t (f a)).Dom
        . simp_all only [Part.getOrElse_of_dom]
        . simp_all only [not_false_eq_true, Part.getOrElse_of_not_dom]
      . exact RA.Query.evaluate.validSchema q left (Sum.elim t default ∘ Sum.inl ∘ f) h_RA_eval

/-- Proof for the tuple evaluation equivalence of the RA to FOL conversion for the Rename operation. -/
theorem toFOL.evalT_def.r_def_eq (h : RA.Query.isWellTyped dbi.schema (.r f q))
  (ih: (toFOL dbi.schema q).evaluateT dbi = RA.Query.evaluateT dbi q) :
    (toFOL dbi.schema (.r f q)).evaluateT dbi = RA.Query.evaluateT dbi (.r f q) := by
      ext t
      apply Iff.intro
      . exact toFOL.evalT_def.r_def.mp h
          (λ t' => ((Set.ext_iff.mp ih) t').mp)
          t
      . exact toFOL.evalT_def.r_def.mpr h
          (λ t' => ((Set.ext_iff.mp ih) t').mpr)
          t
