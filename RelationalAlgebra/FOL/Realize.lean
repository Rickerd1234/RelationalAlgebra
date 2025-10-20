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
theorem BoundedQuery.Realize.exs_def [folStruc dbi] {n : ℕ} (q : BoundedQuery dbs n) {t: Attribute → Value}
  : (exs q).Realize dbi t (default : Fin 0 → Value) ↔ ∃iv : Fin n → Value, q.Realize dbi t iv := by
    simp_all only [Realize, toFormula_exs, Formula.boundedFormula_realize_eq_realize]
    exact BoundedFormula.realize_exs

@[simp]
theorem BoundedQuery.Realize.relabel_formula {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbs n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Attribute → Value}
  {xs : Fin (m + n) → Value} :
  (φ.relabel g).Realize dbi t xs ↔
    (φ.toFormula.relabel g).Realize t xs := by
      simp [Realize]

-- -- Realize a query, without any additional attributes in the 'tuple'
section RealizeMin
variable (dbi : DatabaseInstance) (φ : Query dbi.schema) [folStruc dbi] (t : Tuple)

nonrec def Query.RealizeMin : Prop :=
  ∃(h : t.Dom = φ.schema), (φ.Realize dbi (TupleToFun h) default)

theorem Query.RealizeMin.ex_def :
  Query.RealizeMin dbi φ t ↔ ∃(h : t.Dom = φ.schema), (φ.Realize dbi (TupleToFun h) default) := by
    rfl

theorem Query.RealizeMin.and_def :
  Query.RealizeMin dbi φ t ↔ (t.Dom = φ.schema ∧ ((h : t.Dom = φ.schema) → (φ.Realize dbi (TupleToFun h) default))) := by
    simp only [Query.RealizeMin.ex_def]
    apply Iff.intro
    . intro ⟨w, h⟩
      simp_all only [imp_self, and_self]
    . intro a
      simp_all only [exists_const]

end RealizeMin
