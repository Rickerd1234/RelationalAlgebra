import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Relabel

open FOL FirstOrder Language RM Term

namespace FOL

def Term.realizeSome (dbi) [folStruc dbi] {n : ℕ} (t : fol.Term (Attribute ⊕ (Fin n))) (tup : Tuple) (iv : Fin n →. Value) : Prop
  := (t.realize (Sum.elim tup iv)).Dom

@[simp]
theorem Term.realizeSome.def (dbi) [folStruc dbi] (t : fol.Term (Attribute ⊕ (Fin n))) (tup : Tuple) (iv : Fin n →. Value) :
  Term.realizeSome dbi t tup iv ↔ (t.realize (Sum.elim tup iv)).Dom := by rfl

@[simp]
theorem Term.RealizeSome.fromRelMap [struc : folStruc dbi] (i) {tMap : Fin (dbi.schema rn).card → fol.Term (Attribute ⊕ Fin n)} {tup : Tuple} {iv : Fin n →. Value}
  (h_rel : (struc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim tup iv) (tMap i))))
  : Term.realizeSome dbi (tMap i) tup iv := by
      simp_all only [folStruc_apply_RelMap, realizeSome.def]
      apply Part.dom_iff_mem.mpr
      have ⟨a', ha'⟩ : ∃a', a' = ((dbi.schema rn).fromIndex i) := by simp
      have ⟨t', ht'⟩ : ∃t', t' = (ArityToTuple fun i ↦ realize (Sum.elim tup iv) (tMap i)) := by simp
      have t'_Dom : a' ∈ t'.Dom := by
        simp [RelationInstance.validSchema (dbi.relations rn) t' (by simp_all only), ha']
      use (t' a').get t'_Dom
      subst ht' ha'
      simp_all only [folStruc_apply_RelMap, arityToTuple_def]
      apply Part.get_mem

-- Formal realization definition
def BoundedQuery.Realize (dbi) {n : ℕ} [folStruc dbi] (q : BoundedQuery dbs n): Tuple → (Fin n →. Value) → Prop :=
  q.toFormula.Realize

theorem BoundedQuery.Realize.def [folStruc dbi] {tup : Tuple} {iv : Fin n →. Value} {q : BoundedQuery dbs n}
  : q.Realize dbi tup iv ↔ q.toFormula.Realize tup iv := by rfl

@[simp]
theorem BoundedQuery.Realize.all_att_R_def [folStruc dbi] {tup : Tuple} {iv : Fin n →. Value}
  (h_rel : (R rn tMap).Realize dbi tup iv) (ha : a ∈ dbi.schema rn) :
    Term.realizeSome dbi (tMap ((dbi.schema rn).index ha)) tup iv := by
      simp_all
      exact Term.RealizeSome.fromRelMap ?_ h_rel

@[simp]
theorem BoundedQuery.Realize.exists_t_R_def [folStruc dbi] {tup : Tuple} {iv : Fin n →. Value}
  {tMap : Fin (dbi.schema rn).card → fol.Term (Attribute ⊕ Fin n)}
  (h : dbi.schema rn ≠ ∅)
  (h_rel : (R rn tMap).Realize dbi tup iv) :
    (∃t : fol.Term (Attribute ⊕ (Fin n)), Term.realizeSome dbi t tup iv) := by
      simp_all only [ne_eq, «def», toFormula_rel, BoundedFormula.realize_rel,
        realizeSome.def]
      induction h' : (dbi.schema rn).card with
      | zero => simp_all only [Finset.card_eq_zero]
      | succ k ih =>
        use (tMap (Fin.cast h'.symm (Fin.ofNat' (k + 1) (k + 1))))
        exact Term.RealizeSome.fromRelMap ?_ h_rel

@[simp]
theorem BoundedQuery.Realize.exists_tuple_R_def [folStruc dbi] {tup : Tuple} {iv : Fin n →. Value}
  (h_rel : (R rn tMap).Realize dbi tup iv)
  : (∃t' ∈ (dbi.relations rn).tuples, ∀i, (tMap i).realize (Sum.elim tup iv) = t' ((dbi.schema rn).fromIndex i)) := by
    simp_all only [«def», toFormula_rel, BoundedFormula.realize_rel, folStruc_apply_RelMap]
    use (ArityToTuple fun i ↦ realize (Sum.elim tup iv) (tMap i))
    simp_all only [true_and]
    intro i
    simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def, and_self]

@[simp]
theorem BoundedQuery.Realize.exs_def [folStruc dbi] {n : ℕ} (q : BoundedQuery dbs n) {t: Tuple}
  : (exs q).Realize dbi t (default : Fin 0 →. Value) ↔ ∃iv : Fin n →. Value, q.Realize dbi t iv := by
    simp_all only [«def», toFormula_exs, Formula.boundedFormula_realize_eq_realize]
    exact BoundedFormula.realize_exs

theorem BoundedQuery.Realize.mapTermRel_add_castLe {dbi} [struc : folStruc dbi] {k : ℕ}
    {ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (k + n)))}
    {n} {φ : BoundedQuery dbs n} (v : ∀ {n}, (Fin (k + n) →. Value) → Attribute →. Value)
    {v' : Tuple} (xs : Fin (k + n) →. Value)
    (h1 :
      ∀ (n) (t : fol.Term (Attribute ⊕ (Fin n))) (xs' : Fin (k + n) →. Value),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (hv : ∀ (n) (xs : Fin (k + n) →. Value) (x : Part Value), @v (n + 1) (Fin.snoc xs x : Fin _ →. Value) = v xs) :
    (φ.mapTermRel ft fun _ => BoundedQuery.castLE (add_assoc _ _ _).symm.le).Realize dbi v' xs ↔
      φ.Realize dbi (v xs) (xs ∘ Fin.natAdd _) := by
        induction φ with
        | R => simp [FOL.BoundedQuery.mapTermRel, h1, BoundedQuery.Realize.def]
        | tEq t₁ t₂ => simp_all only [mapTermRel, «def», toFormula_tEq, BoundedFormula.Realize]
        | and _ _ ih1 ih2 => simp_all [FOL.BoundedQuery.mapTermRel, ih1, ih2, BoundedQuery.Realize.def]
        | ex _ ih => simp_all [FOL.BoundedQuery.mapTermRel, ih, hv, BoundedQuery.Realize.def]
        | or _ _ ih1 ih2 => simp_all [FOL.BoundedQuery.mapTermRel, ih1, ih2, BoundedQuery.Realize.def]
        | not _ ih => simp_all [FOL.BoundedQuery.mapTermRel, ih, hv, BoundedQuery.Realize.def]

theorem BoundedQuery.Realize.relabel_formula {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbs n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Tuple}
  {xs : Fin (m + n) →. Value} :
  (φ.relabel g).Realize dbi t xs ↔
    (φ.toFormula.relabel g).Realize t xs := by
      simp [Realize.def]

@[simp]
theorem BoundedQuery.Realize.relabel_def {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbs n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Tuple}
  {xs : Fin (m + n) →. Value} :
  (φ.relabel g).Realize dbi t xs ↔
    φ.Realize dbi (Sum.elim t (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
      simp [Realize.def]

@[simp]
theorem BoundedQuery.Realize.tuple_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery dbs n} {t t' : Tuple} {xs : Fin n →. Value} :
  t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs) := by
    intro h
    rw [h]

@[simp]
theorem BoundedQuery.Realize.assignment_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery dbs n} {t t' : Tuple} {xs xs' : Fin n →. Value} :
  xs = xs' → t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs') := by
    intro h h'
    rw [h, h']

-- -- Realize a query, without any additional attributes in the 'tuple'
nonrec def Query.RealizeMin (dbi : DatabaseInstance) (φ : Query dbi.schema) [folStruc dbi] (t : Tuple) : Prop :=
  φ.Realize dbi t default ∧ t.Dom = φ.schema

@[simp]
theorem Query.RealizeMin.def [folStruc dbi] (φ : Query dbi.schema)
  : φ.RealizeMin dbi t ↔ BoundedQuery.Realize dbi φ t default ∧ t.Dom = φ.schema := by rfl
