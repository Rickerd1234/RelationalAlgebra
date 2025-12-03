import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.Equivalence.FOLtoRA.FRan

open RM FOL FirstOrder Language

@[simp]
def RealizeDomSet {dbi : DatabaseInstance String String μ} [folStruc dbi] [Nonempty μ]
  (q : (fol dbi.schema).BoundedFormula String n) (rs brs : Finset String) (t : String →. μ) (h : t.Dom = rs) : Prop :=
    q.Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) ∧ t.ran ⊆ dbi.domain
