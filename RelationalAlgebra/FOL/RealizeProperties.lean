import RelationalAlgebra.FOL.Realize

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem BoundedQuery.Realize.enlarge [folStruc dbi] {rs rs' : RelationSchema} {tup tup' : Tuple} {iv : Fin n → Value} {q : BoundedQuery dbi.schema n}
  (h_sub : tup'.Dom ⊆ tup.Dom)
  (h_res : tup.restrict h_sub = tup')
  (h_min : ↑q.schema ⊆ tup'.Dom)
  {h' : rs' = tup'.Dom}
  {h : rs = tup.Dom}
  : q.Realize dbi (TupleToFun h'.symm) iv ↔ q.Realize dbi (TupleToFun h.symm) iv := by
    induction q with
    | R rn vMap =>
      simp only [Realize, toFormula, fol.Rel, BoundedFormula.realize_rel, folStruc.RelMap_R,
        ArityToTuple.def_dite]
      rw [@iff_eq_eq]
      apply congr rfl
      ext a v
      simp_all only [schema.R_def, Set.coe_toFinset]
      apply Iff.intro
      · intro a_1
        split
        next h =>
          simp_all only [↓reduceDIte]
          have := Term.cases (vMap (RelationSchema.index h))
          simp_all only [Sum.exists]
          cases this with
          | inl h_1 =>
            obtain ⟨w, h_1⟩ := h_1
            simp_all [realize_var, Sum.elim_inl]
            by_cases hc : (tup w).Dom
            . by_cases hd : (tup' w).Dom
              . simp_all [Part.getOrElse_of_dom]
                congr
                rw [← h_res]
                ext v
                simp [PFun.mem_restrict]
                intro a_2
                subst a_1
                rw [← PFun.mem_dom]
                exact hd
              . simp_all [Part.getOrElse_of_not_dom, Part.getOrElse_of_dom]
                have contra : w ∈ {a | ∃ i, a ∈ (vMap i).varFinsetLeft} := by simp_all; use (RelationSchema.index h); simp_all
                exact False.elim (hd (h_min contra))
            . have : ¬(tup' w).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom]; exact fun a ↦ hc (h_sub a)
              simp_all [Part.getOrElse_of_not_dom]
          | inr h_2 =>
            obtain ⟨w, h_1⟩ := h_2
            simp_all only [realize_var, Sum.elim_inr]
        next h => simp_all only [↓reduceDIte, Part.notMem_none]
      · intro a_1
        split
        next ha =>
          simp_all only [↓reduceDIte]
          have := Term.cases (vMap (RelationSchema.index ha))
          simp_all only [Sum.exists]
          cases this with
          | inl h_1 =>
            obtain ⟨w, h_1⟩ := h_1
            simp_all only [realize_var, Sum.elim_inl]
            simp [Set.subset_def, PFun.mem_dom] at h_min
            have ⟨v', h_2⟩ := h_min w (RelationSchema.index ha) (by simp_all only [varFinsetLeft.eq_1, Finset.mem_singleton])
            simp_all only [Part.mem_some_iff]
            subst a_1
            have t'_dom : (PFun.restrict tup h_sub).Dom = rs ∩ rs' := by
              simp_all only [Finset.coe_inter, Set.right_eq_inter]
            have : Fintype ↑(PFun.restrict tup h_sub).Dom := by
              exact Fintype.ofFinset (rs ∩ rs') (Set.ext_iff.mp t'_dom.symm)
            rw [TupleToFun.tuple_eq h'.symm t'_dom h_res.symm]
            rw [← h_res, PFun.mem_restrict] at h_2
            simp [TupleToFun]
            simp_all only [PFun.mem_dom, Part.getOrElse]
            have : (tup w).Dom := by simp_all [Part.dom_iff_mem]; use v'; exact h_2.2
            have : (tup' w).Dom := by simp_all [Part.dom_iff_mem]
            simp_all
            congr
            simp only [← h_res, Part.ext_iff, PFun.mem_restrict]
            intro a_1
            simp_all only [Finset.coe_inter, Set.right_eq_inter, PFun.mem_dom, true_and]
          | inr h_2 =>
            obtain ⟨w, h_1⟩ := h_2
            simp_all only [realize_var, Sum.elim_inr]
        next h => simp_all only [↓reduceDIte, Part.notMem_none]

    | tEq t₁ t₂ =>
      simp_all [Realize, BoundedFormula.Realize]
      have ⟨t₁, ht₁⟩ := Term.cases t₁
      have ⟨t₂, ht₂⟩ := Term.cases t₂
      subst ht₁ ht₂
      simp_all
      obtain ⟨left, right⟩ := h_min
      unfold TupleToFun
      cases t₁ with
      | inl val =>
        simp_all only [varFinsetLeft, Finset.coe_singleton, Set.singleton_subset_iff, PFun.mem_dom,
          Sum.elim_inl]
        obtain ⟨w, h_1⟩ := left
        have t1 : (tup val).Dom := by simp_all [Part.dom_iff_mem]; use w; rw [← h_res, PFun.mem_restrict] at h_1; exact h_1.2
        have t2 : (tup' val).Dom := by simp_all [Part.dom_iff_mem]; use w

        cases t₂ with
        | inl
          val_1 =>
          simp_all only [varFinsetLeft, Finset.coe_singleton, Set.singleton_subset_iff,
            PFun.mem_dom, Sum.elim_inl]
          obtain ⟨w_1, h_2⟩ := right
          have t3 : (tup val_1).Dom := by simp_all [Part.dom_iff_mem]; use w_1; rw [← h_res, PFun.mem_restrict] at h_2; exact h_2.2
          have t4 : (tup' val_1).Dom := by simp_all [Part.dom_iff_mem]; use w_1
          simp_all [Part.getOrElse]
          simp [Part.get_eq_iff_eq_some, ← h_res]
          rw [@Part.ext_iff]
          simp [PFun.mem_restrict, PFun.mem_dom, ← Part.dom_iff_mem, t2, t4, Part.ext_iff]
          simp_all only [true_and]

        | inr
          val_2 =>
          simp_all only [varFinsetLeft, Finset.coe_empty, Set.empty_subset, Sum.elim_inr]
          simp_all [Part.getOrElse]
          simp [Part.get_eq_iff_eq_some, ← h_res]
          rw [@Part.ext_iff]
          simp [PFun.mem_restrict, PFun.mem_dom, ← Part.dom_iff_mem, t2, Part.ext_iff]
          simp_all only [true_and]

      | inr val_1 =>
        cases t₂ with
        | inl
          val =>
          simp_all only [varFinsetLeft, Finset.coe_empty, Set.empty_subset, Finset.coe_singleton,
            Set.singleton_subset_iff, PFun.mem_dom, Sum.elim_inr, Sum.elim_inl]
          obtain ⟨w, h_1⟩ := right
          have t3 : (tup val).Dom := by simp_all [Part.dom_iff_mem]; use w; rw [← h_res, PFun.mem_restrict] at h_1; exact h_1.2
          have t4 : (tup' val).Dom := by simp_all [Part.dom_iff_mem]; use w
          simp_all [Part.getOrElse]
          simp [← h_res]
          rw [@Part.eq_get_iff_mem]
          simp [PFun.mem_restrict, PFun.mem_dom, ← Part.dom_iff_mem, t4, Part.eq_get_iff_mem]
          intro a
          simp_all only

        | inr val_2 => simp_all only [varFinsetLeft, Finset.coe_empty, Set.empty_subset, Sum.elim_inr]

    | _ => simp_all [Realize]
