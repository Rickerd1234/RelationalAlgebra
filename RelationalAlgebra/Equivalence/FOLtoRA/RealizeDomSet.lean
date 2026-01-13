import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.Equivalence.FOLtoRA.FRan

open RM FOL FirstOrder Language

/--
Whether a `BoundedFormula` is satisfied by a tuple `t` given `t.Dom = rs`
  AND whether all values of `t` are part of the active domain.
-/
@[simp]
def RealizeDomSet {dbi : DatabaseInstance ρ α μ} [LinearOrder α] [Inhabited α] [folStruc dbi] [Inhabited μ]
  (q : (fol dbi.schema).BoundedFormula α n) (rs brs : Finset α) (t : α →. μ) (h : t.Dom = rs) : Prop :=
    q.Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) ∧ t.ran ⊆ dbi.domain
