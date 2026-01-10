import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Relabel

open FOL FirstOrder Language RM Term

namespace FOL

variable {ρ μ : Type} {dbi : DatabaseInstance ρ String μ}

/--
Formal 'realization' definition, uses `BoundedFormula.Realize`.
Essentially a satisfiability check for a given `BoundedQuery`, named variables assignment `String → μ` and bound variables assignment `Fin n → μ`.
-/
def BoundedQuery.Realize (dbi : DatabaseInstance ρ String μ) {n : ℕ} [folStruc dbi] (q : BoundedQuery dbi.schema n) : (String → μ) → (Fin n → μ) → Prop :=
  q.toFormula.Realize

@[simp]
theorem BoundedQuery.Realize.exs_def [folStruc dbi] {n : ℕ} (q : BoundedQuery dbi.schema n) {t: String → μ}
  : (exs q).Realize dbi t (default : Fin 0 → μ) ↔ ∃iv : Fin n → μ, q.Realize dbi t iv := by
    simp_all only [Realize, toFormula_exs, Formula.boundedFormula_realize_eq_realize]
    exact BoundedFormula.realize_exs

@[simp]
theorem BoundedQuery.Realize.relabel_formula {dbi : DatabaseInstance ρ String μ} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery dbi.schema n}  {g : String → String ⊕ (Fin m)} {t : String → μ}
  {xs : Fin (m + n) → μ} :
  (φ.relabel g).Realize dbi t xs ↔
    (φ.toFormula.relabel g).Realize t xs := by
      simp [Realize]

-- Realize a query, without any additional attributes in the 'tuple'
section RealizeMin
variable (dbi) (φ : Query dbi.schema) [folStruc dbi] (t : String →. μ) [Nonempty μ]

/--
Minimal 'realization' definition, uses `BoundedQuery.Realize` and the requirement that .
Essentially a satisfiability check for a given `φ : BoundedQuery` and a tuple with the schema of the free variables (`φ.schema`) in the query.
-/
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
