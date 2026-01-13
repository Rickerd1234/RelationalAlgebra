import RelationalAlgebra.FOL.Schema

open FOL FirstOrder Language Term RM

/- Relabeling of variables in a query, most of this code is based on `ModelTheory.BoundedFormula` relabeling logic. -/

namespace FOL

variable {ρ : Type} {dbs : ρ → Finset α}

/-- Maps bounded queries along a map of terms and a map of relations. -/
def BoundedQuery.mapTermRel {g : ℕ → ℕ} (ft : ∀ n, (fol dbs).Term (α ⊕ (Fin n)) → (fol dbs).Term (α ⊕ (Fin (g n))))
    (h : ∀ n, BoundedQuery dbs (g (n + 1)) → BoundedQuery dbs (g n + 1)) :
    ∀ {n}, BoundedQuery dbs n → BoundedQuery dbs (g n)
  | _n, .R rn vMap      => .R rn (λ i => ft _ (vMap i))
  | _n, .tEq a b        => .tEq (ft _ a) (ft _ b)
  | _n, .and q1 q2      => .and (q1.mapTermRel ft h) (q2.mapTermRel ft h)
  | n,  .ex q           => (h n (q.mapTermRel ft h)).ex
  | _n, .or q1 q2       => .or (q1.mapTermRel ft h) (q2.mapTermRel ft h)
  | _n, .not q          => (q.mapTermRel ft h).not

/-- Casts `BoundedQuery dbs m` as `BoundedQuery dbs n`, where `m ≤ n`. -/
@[simp]
def BoundedQuery.castLE : ∀ {m n : ℕ} (_h : m ≤ n), BoundedQuery dbs m → BoundedQuery dbs n
  | _m, _n, h, .R rn vMap => .R rn (Term.relabel (Sum.map id (Fin.castLE h)) ∘ vMap)
  | _m, _n, h, .tEq a b => .tEq (a.relabel (Sum.map id (Fin.castLE h))) (b.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, .and q₁ q₂ => (q₁.castLE h).and (q₂.castLE h)
  | _m, _n, h, .ex q => (q.castLE (add_le_add_right h 1)).ex
  | _m, _n, h, .or q₁ q₂ => (q₁.castLE h).or (q₂.castLE h)
  | _m, _n, h, .not q => (q.castLE h).not

/- Helper theorems for `castLE` and `mapTermRel` -/
@[simp]
theorem BoundedQuery.castLE_formula {m n} (_h : m ≤ n) (φ : BoundedQuery dbs m) :
  (φ.castLE _h).toFormula = φ.toFormula.castLE _h := by
    revert n
    induction φ
    all_goals intros; simp_all [BoundedQuery.toFormula]; try rfl

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : BoundedQuery dbs n) : φ.castLE h = φ := by
  induction φ with
  | R => simp
  | tEq _ _ => simp
  | and _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | ex _ ih => simp [ih]
  | or _ _ ih₁ ih₂ => simp [ ih₁, ih₂]
  | not _ ih => simp [ih]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : BoundedQuery dbs k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | _ => aesop

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedQuery.castLE mn ∘ BoundedQuery.castLE km :
        BoundedQuery dbs k → BoundedQuery dbs n) =
      BoundedQuery.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

@[simp]
theorem BoundedQuery.mapTermRel_formula {g : ℕ → ℕ} (ft : ∀ n, (fol dbs).Term (α ⊕ (Fin n)) → (fol dbs).Term (α ⊕ (Fin (g n))))
    (h : ∀n, g (n + 1) ≤ g n + 1) (φ : BoundedQuery dbs m) :
  (φ.mapTermRel ft (λ n => castLE (h n))).toFormula = φ.toFormula.mapTermRel ft (λ _ => id) (λ n => BoundedFormula.castLE (h n)) := by
    induction φ
    all_goals simp_all only [mapTermRel, BoundedQuery.toFormula, castLE_formula]; rfl


/-- Raises all of the `Fin`-indexed variables of a query greater than or equal to `m` by `n'`. -/
def BoundedQuery.liftAt : ∀ {n : ℕ} (n' _m : ℕ), BoundedQuery dbs n → BoundedQuery dbs (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

/-- Relabels a bounded query's variables along a particular function. -/
def BoundedQuery.relabel (g : α → α ⊕ (Fin n)) {k} (φ : BoundedQuery dbs k) : BoundedQuery dbs (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (BoundedFormula.relabelAux g _)) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/- Helper theorems for relabeling -/
@[simp]
theorem BoundedQuery.relabel.R_def (g : α → α ⊕ (Fin n)) :
  (R rn t).relabel g = R rn (fun i => (t i).relabel (BoundedFormula.relabelAux g _)) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.tEq_def (g : α → α ⊕ (Fin n)) {k} (t₁ t₂ : (fol dbs).Term (α ⊕ (Fin k))) :
  (tEq t₁ t₂ : BoundedQuery dbs k).relabel g = tEq (t₁.relabel (BoundedFormula.relabelAux g _)) (t₂.relabel (BoundedFormula.relabelAux g _)) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.and_def (g : α → α ⊕ (Fin n)) {k} (φ ψ : BoundedQuery dbs k) :
  (and φ ψ).relabel g = and (φ.relabel g) (ψ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.ex_def (g : α → α ⊕ (Fin n)) {k} (φ : BoundedQuery dbs (k + 1)) :
  (ex φ).relabel g = ex (φ.relabel g) := by
    rw [relabel, mapTermRel, relabel]
    simp

@[simp]
theorem BoundedQuery.relabel.or_def (g : α → α ⊕ (Fin n)) {k} (φ ψ : BoundedQuery dbs k) :
  (or φ ψ).relabel g = or (φ.relabel g) (ψ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel.not_def (g : α → α ⊕ (Fin n)) {k} (φ : BoundedQuery dbs k) :
  (not φ).relabel g = not (φ.relabel g) := by
    rfl

@[simp]
theorem BoundedQuery.relabel_formula (g : α → α ⊕ (Fin n)) {k} (φ : BoundedQuery dbs k) :
  (φ.relabel g).toFormula = φ.toFormula.relabel g := by
    simp only [relabel, BoundedFormula.relabelAux, mapTermRel_formula, BoundedFormula.relabel]

@[simp]
theorem BoundedQuery.relabel_Sum_inl {k} {h : k ≤ n + k} (φ : BoundedQuery dbs k) (h' : n = 0) :
  (φ.relabel (λ t => (Sum.inl t : (α ⊕ Fin n)))) = φ.castLE h := by
    simp_all [relabel]
    induction φ with
    | R => subst h'; simp_all only [Fin.natAdd_zero, castLE]; rfl
    | tEq => subst h'; simp_all [mapTermRel]; apply And.intro; all_goals rfl
    | _ => simp_all [mapTermRel]
