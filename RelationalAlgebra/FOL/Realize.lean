import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Relabel

open FOL FirstOrder Language RM Term

namespace FOL

-- Formal realization definition
def BoundedQuery.Realize (dbi) {n : ℕ} [folStruc dbi] (q : BoundedQuery dbs n): (Attribute → Value) → (Fin n → Value) → Prop :=
  q.toFormula.Realize

@[simp]
theorem BoundedQuery.Realize.exists_tuple_R_def [folStruc dbi] {tup : Attribute → Value} {iv : Fin n → Value}
  (h_rel : (R rn tMap).Realize dbi tup iv)
  : (∃t' ∈ (dbi.relations rn).tuples, ∀i, (tMap i).realize (Sum.elim tup iv) = t' ((dbi.schema rn).fromIndex i)) := by
    simp_all only [Realize, toFormula_rel, BoundedFormula.realize_rel, folStruc_apply_RelMap]
    use (ArityToTuple fun i ↦ realize (Sum.elim tup iv) (tMap i))
    simp_all only [true_and]
    intro i
    simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def, and_self]

@[simp]
theorem BoundedQuery.Realize.exs_def [folStruc dbi] {n : ℕ} (q : BoundedQuery dbs n) {t: Attribute → Value}
  : (exs q).Realize dbi t (default : Fin 0 → Value) ↔ ∃iv : Fin n → Value, q.Realize dbi t iv := by
    simp_all only [Realize, toFormula_exs, Formula.boundedFormula_realize_eq_realize]
    exact BoundedFormula.realize_exs

theorem BoundedQuery.Realize.mapTermRel_add_castLe {dbi} [struc : folStruc dbi] {k : ℕ}
    {ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (k + n)))}
    {n} {φ : BoundedQuery dbs n} (v : ∀ {n}, (Fin (k + n) → Value) → Attribute → Value)
    {v' : Attribute → Value} (xs : Fin (k + n) → Value)
    (h1 :
      ∀ (n) (t : fol.Term (Attribute ⊕ (Fin n))) (xs' : Fin (k + n) → Value),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (hv : ∀ (n) (xs : Fin (k + n) → Value) (x : Value), @v (n + 1) (Fin.snoc xs x : Fin _ → Value) = v xs) :
    (φ.mapTermRel ft fun _ => BoundedQuery.castLE (add_assoc _ _ _).symm.le).Realize dbi v' xs ↔
      φ.Realize dbi (v xs) (xs ∘ Fin.natAdd _) := by
        induction φ with
        | R => simp [FOL.BoundedQuery.mapTermRel, h1, Realize]
        | tEq t₁ t₂ => simp_all only [mapTermRel, Realize, toFormula_tEq, BoundedFormula.Realize]
        | and _ _ ih1 ih2 => simp_all [FOL.BoundedQuery.mapTermRel, ih1, ih2, Realize]
        | ex _ ih => simp_all [FOL.BoundedQuery.mapTermRel, ih, hv, Realize]
        | or _ _ ih1 ih2 => simp_all [FOL.BoundedQuery.mapTermRel, ih1, ih2, Realize]
        | not _ ih => simp_all [FOL.BoundedQuery.mapTermRel, ih, hv, Realize]

theorem BoundedQuery.Realize.relabel_formula {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbs n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Attribute → Value}
  {xs : Fin (m + n) → Value} :
  (φ.relabel g).Realize dbi t xs ↔
    (φ.toFormula.relabel g).Realize t xs := by
      simp [Realize]

@[simp]
theorem BoundedQuery.Realize.relabel_def {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbs n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Attribute → Value}
  {xs : Fin (m + n) → Value} :
  (φ.relabel g).Realize dbi t xs ↔
    φ.Realize dbi (Sum.elim t (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
      simp [Realize]

@[simp]
theorem BoundedQuery.Realize.tuple_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery dbs n} {t t' : Attribute → Value} {xs : Fin n → Value} :
  t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs) := by
    intro h
    rw [h]

@[simp]
theorem BoundedQuery.Realize.assignment_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery dbs n} {t t' : Attribute → Value} {xs xs' : Fin n → Value} :
  xs = xs' → t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs') := by
    intro h h'
    rw [h, h']

-- -- Realize a query, without any additional attributes in the 'tuple'

nonrec def Query.RealizeMin (dbi : DatabaseInstance) (φ : Query dbi.schema) [folStruc dbi] (t : Tuple) : Prop :=
  ∃(h : t.Dom = φ.schema), (φ.Realize dbi (TupleToFun h) default)

theorem Query.RealizeMin.ex_def (dbi : DatabaseInstance) (φ : Query dbi.schema) [folStruc dbi] (t : Tuple) :
  Query.RealizeMin dbi φ t ↔ ∃(h : t.Dom = φ.schema), (φ.Realize dbi (TupleToFun h) default) := by
    rfl

theorem Query.RealizeMin.and_def (dbi : DatabaseInstance) (φ : Query dbi.schema) [folStruc dbi] (t : Tuple) :
  Query.RealizeMin dbi φ t ↔ (t.Dom = φ.schema ∧ ((h : t.Dom = φ.schema) → (φ.Realize dbi (TupleToFun h) default))) := by
    simp [Query.RealizeMin.ex_def]
    apply Iff.intro
    . intro ⟨w, h⟩
      simp_all only [imp_self, and_self]
    . intro a
      simp_all only [exists_const]
