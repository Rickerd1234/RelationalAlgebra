import RelationalAlgebra.FOL.ModelTheory

open FOL FirstOrder Language Term RM

namespace FOL

@[simp]
theorem fol.Term.relabelAux_sumInl {n k} (g : Attribute → Attribute ⊕ (Fin n)) {i a : Attribute} :
  BoundedFormula.relabelAux g k (Sum.inl i) = Sum.inl a ↔ g i = Sum.inl a := by
    simp [BoundedFormula.relabelAux]
    apply Iff.intro
    · intro a_1
      simp_all [Equiv.sumAssoc, finSumFinEquiv]
      by_cases h : (g i).isLeft
      . simp_all [Sum.isLeft_iff]
        obtain ⟨w, h⟩ := h
        simp_all only [Sum.elim_inl, Sum.map_inl, id_eq, Sum.inl.injEq]
      . simp_all [Sum.isRight_iff]
        obtain ⟨w, h⟩ := h
        simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr, Sum.elim_inl, reduceCtorEq]
    · intro a_1
      simp_all only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, id_eq]

@[simp]
theorem fol.Term.relabelAux_castLE {n} [folStruc] {g : Attribute → Attribute ⊕ Fin k} {t : fol.Term (Attribute ⊕ Fin n)} :
  (Term.relabel (Sum.map id (Fin.castLE (Nat.le_add_right (k + n) 1)) ∘ BoundedFormula.relabelAux g n) t) =
    (Term.relabel (BoundedFormula.relabelAux g (n + 1) ∘ Sum.map id (Fin.castLE (Nat.le_add_right n 1))) t) := by
      -- induction t
      have ⟨t, ht⟩ := Term.cases t
      subst ht
      simp_all only [relabel, Function.comp_apply, var.injEq]
      cases t with
      | inl val =>
        simp_all only [Sum.map_inl, id_eq, BoundedFormula.relabelAux]
        by_cases h : (g val).isLeft
        . simp_all [Sum.isLeft_iff]
          aesop
        . simp_all [Sum.isRight_iff]
          aesop
      | inr val_1 =>
        simp_all only [Sum.map_inr]
        rfl

@[simp]
theorem fol.Term.relabel_varFinsetLeft_id [folStruc] {k n} {f : Fin k → Fin n} {t : fol.Term (Attribute ⊕ Fin k)} :
  (Term.relabel (Sum.map id f) t).varFinsetLeft = t.varFinsetLeft := by
    ext a
    unfold varFinsetLeft
    apply Iff.intro
    · intro a_1
      split
      next x i => simp_all only [relabel, Sum.map_inl, id_eq, Finset.mem_singleton]
      next x _i => simp_all only [relabel, Sum.map_inr, Finset.not_mem_empty]
      next x l _f ts => exact False.elim (folStruc_empty_fun _f)
    · intro a_1
      split
      next x i heq =>
        simp_all only [Finset.mem_singleton]
        split at a_1
        next x_1 i_1 => simp_all only [relabel, Sum.map_inl, id_eq, var.injEq, Sum.inl.injEq, Finset.mem_singleton]
        next x_1 _i => simp_all only [relabel, Sum.map_inr, var.injEq, reduceCtorEq]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x _i heq =>
        simp_all only [Finset.not_mem_empty]
        split at a_1
        next x_1 i => simp_all only [relabel, Sum.map_inl, id_eq, var.injEq, reduceCtorEq]
        next x_1 _i_1 => simp_all only [relabel, Sum.map_inr, var.injEq, Sum.inr.injEq, Finset.not_mem_empty]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x l _f ts heq =>
        exact False.elim (folStruc_empty_fun _f)

@[simp]
theorem fol.Term.relabel_varFinsetLeft_relabelAux [folStruc] {k n} (g : Attribute → Attribute ⊕ (Fin n)) (t : fol.Term (Attribute ⊕ Fin k)) :
  (Term.relabel (BoundedFormula.relabelAux g _) t).varFinsetLeft = t.varFinsetLeft.pimage (λ a => (g a).getLeft?) := by
    simp [Finset.pimage]
    ext a
    simp_all only [Finset.mem_biUnion, Part.mem_toFinset, Part.mem_ofOption, Option.mem_def, Sum.getLeft?_eq_some_iff]
    apply Iff.intro
    · intro a_1
      unfold varFinsetLeft at *
      split
      next x i =>
        simp_all only [relabel, Finset.mem_singleton, exists_eq_left]
        split at a_1
        next x_1 i_1 heq =>
          simp_all only [var.injEq, Finset.mem_singleton]
          subst a_1
          simp_all [relabelAux_sumInl]
        next x_1 _i heq => simp_all only [var.injEq, Finset.not_mem_empty]
        next x_1 l _f ts heq => simp_all only [reduceCtorEq]
      next x _i =>
        simp_all only [relabel, Finset.not_mem_empty, false_and, exists_const]
        split at a_1
        next x_1 i heq =>
          simp_all only [var.injEq, Finset.mem_singleton, BoundedFormula.relabelAux]
          subst a_1
          simp_all only [Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, reduceCtorEq]
        next x_1 _i_1 heq => simp_all only [var.injEq, Finset.not_mem_empty]
        next x_1 l _f ts heq => simp_all only [reduceCtorEq]
      next x l _f ts => exact False.elim (folStruc_empty_fun _f)

    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      unfold varFinsetLeft at *
      simp_all [BoundedFormula.relabelAux]
      split
      next x i heq =>
        simp_all only [Finset.mem_singleton]
        split at left
        next x_1 i_1 =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inl, var.injEq, Finset.mem_singleton,
            Equiv.sumAssoc_apply_inl_inl, id_eq, Sum.inl.injEq]
        next x_1 _i =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, var.injEq, reduceCtorEq]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x _i heq =>
        simp_all only [Finset.not_mem_empty]
        split at left
        next x_1 i =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inl, var.injEq, Finset.mem_singleton,
            Equiv.sumAssoc_apply_inl_inl, id_eq, reduceCtorEq]
        next x_1 _i_1 =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, var.injEq, Sum.inr.injEq, Finset.not_mem_empty]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x l _f ts heq =>
        simp_all only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        split at left
        next x_1 i => simp_all only [relabel, Function.comp_apply, Sum.map_inl, reduceCtorEq]
        next x_1 _i =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, reduceCtorEq]
        next x_1 l_1 _f
          ts_1 =>
          simp_all only [relabel, func.injEq, heq_eq_eq, Finset.mem_biUnion, Finset.mem_univ, true_and]
          obtain ⟨left_1, right_1⟩ := heq
          obtain ⟨w_1, h⟩ := left
          obtain ⟨left, right_1⟩ := right_1
          subst left_1 left
          simp_all only [heq_eq_eq]
          subst right_1
          simp_all only
          exact False.elim (folStruc_empty_fun _f)

@[simp]
theorem BoundedFormula.relabel_freeVarFinset [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : fol.BoundedFormula Attribute k) :
  (φ.relabel g).freeVarFinset = (φ.freeVarFinset.pimage (λ a => (g a).getLeft?)) := by
    simp_all only [Finset.pimage]
    induction φ
    . simp_all only [BoundedFormula.relabel_falsum, BoundedFormula.freeVarFinset.eq_1, BoundedFormula.freeVarFinset,
      Finset.biUnion_empty]
    . simp_all only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.freeVarFinset, fol.Term.relabel_varFinsetLeft_relabelAux]
      aesop
    . simp_all only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.freeVarFinset, fol.Term.relabel_varFinsetLeft_relabelAux]
      aesop
    . aesop
    . simp_all only [BoundedFormula.relabel_all, Nat.add_eq, BoundedFormula.freeVarFinset]
