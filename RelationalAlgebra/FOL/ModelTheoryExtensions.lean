import RelationalAlgebra.FOL.ModelTheory
import Mathlib.ModelTheory.Complexity

open FOL FirstOrder Language Term RM

namespace FOL

@[simp]
theorem fol.Term.relabelAux_sumInl {n k} (g : String → String ⊕ (Fin n)) {i a : String} :
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
theorem fol.Term.relabelAux_castLE {g : String → String ⊕ Fin k} {t : (fol dbs).Term (String ⊕ Fin n)} :
  (Term.relabel (Sum.map id (Fin.castLE (Nat.le_add_right (k + n) 1)) ∘ BoundedFormula.relabelAux g n) t) =
    (Term.relabel (BoundedFormula.relabelAux g (n + 1) ∘ Sum.map id (Fin.castLE (Nat.le_add_right n 1))) t) := by
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
theorem fol.Term.relabel_varFinsetLeft_id {k n} {f : Fin k → Fin n} {t : (fol dbs).Term (String ⊕ Fin k)} :
  (Term.relabel (Sum.map id f) t).varFinsetLeft = t.varFinsetLeft := by
    ext a
    unfold varFinsetLeft
    apply Iff.intro
    · intro a_1
      split
      next x i => simp_all only [relabel, Sum.map_inl, id_eq, Finset.mem_singleton]
      next x _i => simp_all only [relabel, Sum.map_inr, Finset.notMem_empty]
      next x l _f ts => exact False.elim (fol_empty_fun _f)
    · intro a_1
      split
      next x i heq =>
        simp_all only [Finset.mem_singleton]
        split at a_1
        next x_1 i_1 => simp_all only [relabel, Sum.map_inl, id_eq, var.injEq, Sum.inl.injEq, Finset.mem_singleton]
        next x_1 _i => simp_all only [relabel, Sum.map_inr, var.injEq, reduceCtorEq]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x _i heq =>
        simp_all only [Finset.notMem_empty]
        split at a_1
        next x_1 i => simp_all only [relabel, Sum.map_inl, id_eq, var.injEq, reduceCtorEq]
        next x_1 _i_1 => simp_all only [relabel, Sum.map_inr, var.injEq, Sum.inr.injEq, Finset.notMem_empty]
        next x_1 l _f ts => simp_all only [relabel, reduceCtorEq]
      next x l _f ts heq =>
        exact False.elim (fol_empty_fun _f)

@[simp]
theorem fol.Term.relabel_varFinsetLeft_relabelAux {k n} (g : String → String ⊕ (Fin n)) (t : (fol dbs).Term (String ⊕ Fin k)) :
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
        next x_1 _i heq => simp_all only [var.injEq, Finset.notMem_empty]
        next x_1 l _f ts heq => simp_all only [reduceCtorEq]
      next x _i =>
        simp_all only [relabel, Finset.notMem_empty, false_and, exists_const]
        split at a_1
        next x_1 i heq =>
          simp_all only [var.injEq, Finset.mem_singleton, BoundedFormula.relabelAux]
          subst a_1
          simp_all only [Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, reduceCtorEq]
        next x_1 _i_1 heq => simp_all only [var.injEq, Finset.notMem_empty]
        next x_1 l _f ts heq => simp_all only [reduceCtorEq]
      next x l _f ts => exact False.elim (fol_empty_fun _f)

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
        simp_all only [Finset.notMem_empty]
        split at left
        next x_1 i =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inl, var.injEq, Finset.mem_singleton,
            Equiv.sumAssoc_apply_inl_inl, id_eq, reduceCtorEq]
        next x_1 _i_1 =>
          simp_all only [relabel, Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
            finSumFinEquiv_apply_right, var.injEq, Sum.inr.injEq, Finset.notMem_empty]
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
          exact False.elim (fol_empty_fun _f)

@[simp]
theorem BoundedFormula.relabel_freeVarFinset {n k} (g : String → String ⊕ (Fin n)) (φ : (fol dbs).BoundedFormula String k) :
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

open BoundedFormula

@[simp]
theorem BoundedFormula.castLE_freeVarFinset {m n} (φ : (fol dbs).BoundedFormula String m) (h : m = n) {h' : m ≤ n} :
  (φ.castLE h').freeVarFinset = φ.freeVarFinset := by
    induction φ with
    | all f ih =>
      rename_i k
      subst h
      simp only [castLE, castLE_rfl, freeVarFinset]
    | _ => simp_all

@[simp]
theorem liftAt_freeVarFinset {n n'} (φ : (fol dbs).BoundedFormula String n) (hmn : m + n' ≤ n + 1) :
  (φ.liftAt n' m).freeVarFinset = φ.freeVarFinset := by
    rw [BoundedFormula.liftAt]
    induction φ with
    | all f ih =>
      rename_i k
      have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
      simp only [mapTermRel, freeVarFinset, castLE_freeVarFinset ?_ h, ih (hmn.trans k.succ.le_succ)]
    | _ => simp_all [mapTermRel, Term.liftAt]

theorem freeVarFinset_toPrenexImpRight {φ ψ : (fol dbs).BoundedFormula String n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    (φ.toPrenexImpRight ψ).freeVarFinset = (φ.imp ψ).freeVarFinset := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    rw [@toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [freeVarFinset, le_refl, liftAt_freeVarFinset]
    exact IsQF.liftAt hφ
  | ex _ ih =>
    rw [@toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [freeVarFinset, le_refl, liftAt_freeVarFinset]
    exact IsQF.liftAt hφ

theorem freeVarFinset_toPrenexImp {φ ψ : (fol dbs).BoundedFormula String n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    (φ.toPrenexImp ψ).freeVarFinset = (φ.imp ψ).freeVarFinset := by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact freeVarFinset_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    rw [toPrenexImp]
    simp_all only [freeVarFinset, Finset.union_empty]
    rw [ih]
    . simp
    . exact IsPrenex.liftAt hψ
  | ex _ ih =>
    rename_i n' φ hφ
    intro ψ hψ
    have : (liftAt 1 n' ψ).IsPrenex := hψ.liftAt
    have := ih this
    simp at *
    exact this

@[simp]
theorem freeVarFinset_toPrenex (φ : (fol dbs).BoundedFormula String n) :
    φ.toPrenex.freeVarFinset = φ.freeVarFinset := by
  induction φ with
  | falsum => exact rfl
  | equal => exact rfl
  | rel => exact rfl
  | imp f1 f2 h1 h2 =>
    rw [toPrenex, freeVarFinset_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, freeVarFinset,
      freeVarFinset, h1, h2]
  | all _ h =>
    rw [freeVarFinset, toPrenex, freeVarFinset, h]

@[simp]
def depth : BoundedFormula L Attribute n → ℕ
  | .falsum => 0
  | .rel _ _ => 0
  | .equal _ _ => 0
  | .imp f₁ f₂ => max (depth f₁) (depth f₂)
  | .all f' => 1 + depth f'

@[simp]
theorem depth.imp_def_left (f₁ f₂ : BoundedFormula L Attribute n) :
  ∃m, n + depth (.imp f₁ f₂) = n + m + depth f₁ := by
    simp
    have := max_cases (depth f₁) (depth f₂)
    simp_all only [sup_eq_left, and_self, sup_eq_right]
    cases this with
    | inl h => simp_all only [sup_of_le_left, Nat.add_right_cancel_iff, Nat.left_eq_add, exists_eq]
    | inr h_1 =>
      simp_all only [sup_of_le_right]
      obtain ⟨left, right⟩ := h_1
      use (depth f₂ - depth f₁)
      grind

theorem depth.imp_comm (f₁ f₂ : BoundedFormula L Attribute n) :
  depth (.imp f₁ f₂) = depth (.imp f₂ f₁) := by simp [max_comm]

@[simp]
theorem depth.imp_def_right (f₁ f₂ : BoundedFormula L Attribute n) :
  ∃m, n + depth (.imp f₁ f₂) = n + m + depth f₂ := by
    rw [depth.imp_comm]
    exact imp_def_left f₂ f₁

@[simp]
theorem depth.all_def (f : BoundedFormula L Attribute (n + 1)) :
  n + depth (.all f) = n + 1 + depth f := by
    simp; grind
