import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.Equivalence.FOLtoRA.FRan

open RM FOL FirstOrder Language

/--
The set of tuples (`t : α →. μ`) satisfying a `BoundedFormula` with given `t.Dom = rs` and `t.ran ⊆ dbi.domain`.
-/
@[simp]
def RealizeDomSet {dbi : DatabaseInstance ρ α μ} [LinearOrder α] [Inhabited α] [folStruc dbi] [Inhabited μ]
  (q : (fol dbi.schema).BoundedFormula α n) (rs brs : Finset α) : Set (α →. μ) :=
    {t : α →. μ | ∃h : t.Dom = rs, q.Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) ∧ t.ran ⊆ dbi.domain}
