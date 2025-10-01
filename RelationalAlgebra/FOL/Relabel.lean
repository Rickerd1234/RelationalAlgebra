import RelationalAlgebra.FOL.Schema

open FOL FirstOrder Language Term RM

namespace FOL

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def BoundedQuery.mapTermRel {g : ℕ → ℕ} (ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (g n))))
    (h : ∀ n, BoundedQuery (g (n + 1)) → BoundedQuery (g n + 1)) :
    ∀ {n}, BoundedQuery n → BoundedQuery (g n)
  | _n, .R dbs rn vMap  => .R dbs rn (λ i => ft _ (vMap i))
  | _n, .tEq q a b      => .tEq (q.mapTermRel ft h) (ft _ a) (ft _ b)
  | _n, .and q1 q2      => .and (q1.mapTermRel ft h) (q2.mapTermRel ft h)
  | n,  .ex q           => (h n (q.mapTermRel ft h)).ex
  | _n, .or q1 q2      => .or (q1.mapTermRel ft h) (q2.mapTermRel ft h)
  | _n, .not q          => (q.mapTermRel ft h).not

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def BoundedQuery.castLE : ∀ {m n : ℕ} (_h : m ≤ n), BoundedQuery m → BoundedQuery n
  | _m, _n, h, .R dbs rn vMap => .R dbs rn (Term.relabel (Sum.map id (Fin.castLE h)) ∘ vMap)
  | _m, _n, h, .tEq q a b => .tEq (q.castLE h) (a.relabel (Sum.map id (Fin.castLE h))) (b.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, .and q₁ q₂ => (q₁.castLE h).and (q₂.castLE h)
  | _m, _n, h, .ex q => (q.castLE (add_le_add_right h 1)).ex
  | _m, _n, h, .or q₁ q₂ => (q₁.castLE h).or (q₂.castLE h)
  | _m, _n, h, .not q => (q.castLE h).not

@[simp]
theorem BoundedQuery.castLE_formula {m n} (_h : m ≤ n) (φ : BoundedQuery m) :
  (φ.castLE _h).toFormula = φ.toFormula.castLE _h := by
    revert n
    induction φ
    all_goals intros; simp_all [BoundedQuery.toFormula]; try rfl

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : BoundedQuery n) : φ.castLE h = φ := by
  induction φ with
  | R => simp [Fin.castLE_of_eq]
  | tEq _ _ _ ih => simp [Fin.castLE_of_eq, ih]
  | and _ _ ih₁ ih₂ => simp [Fin.castLE_of_eq, ih₁, ih₂]
  | ex _ ih => simp [Fin.castLE_of_eq, ih]
  | or _ _ ih₁ ih₂ => simp [Fin.castLE_of_eq, ih₁, ih₂]
  | not _ ih => simp [Fin.castLE_of_eq, ih]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : BoundedQuery k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | _ => aesop

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedQuery.castLE mn ∘ BoundedQuery.castLE km :
        BoundedQuery k → BoundedQuery n) =
      BoundedQuery.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

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
theorem BoundedQuery.relabel.R_def (g : Attribute → Attribute ⊕ (Fin n)) :
  (R dbs rn t).relabel g = R dbs rn (fun i => (t i).relabel (BoundedFormula.relabelAux g _)) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.tEq_def (g : Attribute → Attribute ⊕ (Fin n)) {k} {q : BoundedQuery k} (t₁ t₂ : fol.Term (Attribute ⊕ (Fin k))) :
  (tEq q t₁ t₂).relabel g = tEq (q.relabel g) (t₁.relabel (BoundedFormula.relabelAux g _)) (t₂.relabel (BoundedFormula.relabelAux g _)) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.and_def (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ ψ : BoundedQuery k) :
  (and φ ψ).relabel g = and (φ.relabel g) (ψ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.ex_def (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery (k + 1)) :
  (ex φ).relabel g = ex (φ.relabel g) := by
    rw [relabel, mapTermRel, relabel]
    simp

@[simp]
theorem BoundedQuery.relabel.or_def (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ ψ : BoundedQuery k) :
  (or φ ψ).relabel g = or (φ.relabel g) (ψ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.not_def (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery k) :
  (not φ).relabel g = not (φ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel_formula (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery k) :
  (φ.relabel g).toFormula = φ.toFormula.relabel g := by
    simp only [relabel, BoundedFormula.relabelAux, mapTermRel_formula, BoundedFormula.relabel]

@[simp]
theorem BoundedQuery.relabel_Sum_inl {k} {h : k ≤ n + k} (φ : BoundedQuery k) (h' : n = 0) :
  (φ.relabel (λ t => (Sum.inl t : (Attribute ⊕ Fin n)))) = φ.castLE h := by
    simp_all [relabel, castLE_rfl]
    induction φ with
    | R => subst h'; simp_all only [Fin.natAdd_zero, castLE]; rfl
    | tEq => subst h'; simp_all [mapTermRel]; apply And.intro; all_goals rfl
    | _ => simp_all [mapTermRel]
