import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language Term RM

namespace FOL

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def BoundedQuery.mapTermRel {g : ℕ → ℕ} (ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (g n))))
    (h : ∀ n, BoundedQuery (g (n + 1)) → BoundedQuery (g n + 1)) :
    ∀ {n}, BoundedQuery n → BoundedQuery (g n)
  | _n, .R dbs rn vMap  => .R dbs rn (λ i => ft _ (vMap i))
  | _n, .and q1 q2      => .and (q1.mapTermRel ft h) (q2.mapTermRel ft h)
  | n,  .ex q           => (h n (q.mapTermRel ft h)).ex
  -- | n,  .all q          => (h n (q.mapTermRel ft h)).all
  -- | _n, .not q          => (q.mapTermRel ft h).not

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def BoundedQuery.castLE : ∀ {m n : ℕ} (_h : m ≤ n), BoundedQuery m → BoundedQuery n
  | _m, _n, h, .R dbs rn vMap => .R dbs rn (Term.relabel (Sum.map id (Fin.castLE h)) ∘ vMap)
  | _m, _n, h, .and q₁ q₂ => (q₁.castLE h).and (q₂.castLE h)
  | _m, _n, h, .ex q => (q.castLE (add_le_add_right h 1)).ex
  -- | _m, _n, h, .all q => (q.castLE (add_le_add_right h 1)).all
  -- | _m, _n, h, .not q => (q.castLE h).not

@[simp]
theorem BoundedQuery.castLE_formula {m n} (_h : m ≤ n) (φ : BoundedQuery m) :
  (φ.castLE _h).toFormula = φ.toFormula.castLE _h := by
    revert n
    induction φ
    all_goals intros; simp_all [BoundedQuery.toFormula]; rfl

@[simp]
theorem BoundedQuery.mapTermRel_formula {g : ℕ → ℕ} (ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (g n))))
    (h : ∀n, g (n + 1) ≤ g n + 1) (φ : BoundedQuery m) :
  (φ.mapTermRel ft (λ n => castLE (h n))).toFormula = φ.toFormula.mapTermRel ft (λ _ => id) (λ n => BoundedFormula.castLE (h n)) := by
    induction φ
    all_goals simp_all only [mapTermRel, castLE, BoundedQuery.toFormula, castLE_formula]; rfl

/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def BoundedQuery.liftAt : ∀ {n : ℕ} (n' _m : ℕ), BoundedQuery n → BoundedQuery (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

/-- Relabels a bounded formula's variables along a particular function. -/
def BoundedQuery.relabel (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery k) : BoundedQuery (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (BoundedFormula.relabelAux g _)) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

@[simp]
theorem BoundedQuery.relabel_formula (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery k) :
  (φ.relabel g).toFormula = φ.toFormula.relabel g := by
    simp only [relabel, BoundedFormula.relabelAux, mapTermRel_formula, BoundedFormula.relabel]

-- @TODO: This proof
theorem fol.Term.relabelAux_sumInl {n k} (g : Attribute → Attribute ⊕ (Fin n)) {i a : Attribute} :
  BoundedFormula.relabelAux g k (Sum.inl i) = Sum.inl a ↔ g i = Sum.inl a := by
    simp [BoundedFormula.relabelAux]
    apply Iff.intro
    · intro a_1
      simp_all [Equiv.sumAssoc, finSumFinEquiv]
      sorry
    · intro a_1
      simp_all only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, id_eq]

@[simp]
theorem fol.Term.relabel_varFinsetLeft [folStruc] {k n} (g : Attribute → Attribute ⊕ (Fin n)) (t : fol.Term (Attribute ⊕ Fin k)) :
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
theorem BoundedFormula.exs_freeVarFinset {k} (φ : fol.BoundedFormula Attribute k) :
  (φ.exs).freeVarFinset = φ.freeVarFinset := by
    induction k
    . simp [BoundedFormula.exs]
    . simp [BoundedFormula.exs]
      simp_all only [BoundedFormula.freeVarFinset, Finset.union_empty]

@[simp]
theorem BoundedFormula.relabel_freeVarFinset [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : fol.BoundedFormula Attribute k) :
  (φ.relabel g).freeVarFinset = (φ.freeVarFinset.pimage (λ a => (g a).getLeft?)) := by
    simp_all only [BoundedQuery.relabel_formula, Finset.pimage]
    induction φ
    . simp_all only [BoundedFormula.relabel_falsum, BoundedFormula.freeVarFinset.eq_1, BoundedFormula.freeVarFinset,
      Finset.biUnion_empty]
    . simp_all only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.freeVarFinset, fol.Term.relabel_varFinsetLeft]
      aesop
    . simp_all only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.freeVarFinset, fol.Term.relabel_varFinsetLeft]
      aesop
    . aesop
    . simp_all only [BoundedFormula.relabel_all, Nat.add_eq, BoundedFormula.freeVarFinset]
