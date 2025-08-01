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

/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def BoundedQuery.liftAt : ∀ {n : ℕ} (n' _m : ℕ), BoundedQuery n → BoundedQuery (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

/-- A function to help relabel the variables in bounded formulas. -/
def BoundedQuery.relabelAux (g : Attribute → Attribute ⊕ (Fin n)) (k : ℕ) : Attribute ⊕ (Fin k) → Attribute ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's variables along a particular function. -/
def BoundedQuery.relabel (g : Attribute → Attribute ⊕ (Fin n)) {k} (φ : BoundedQuery k) : BoundedQuery (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))
