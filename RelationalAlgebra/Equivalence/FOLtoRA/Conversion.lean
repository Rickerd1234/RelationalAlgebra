import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.FOL.Query
import Mathlib.ModelTheory.Complexity

open RM FOL FirstOrder Language

def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula Attribute n :=
  q.toFormula.toPrenex

noncomputable def TermtoAtt (rs : RelationSchema) : fol.Term (Attribute ⊕ Fin (rs).card) → Attribute
  | var (Sum.inl a) => a
  | var (Sum.inr i) => RelationSchema.fromIndex i
  | _ => Classical.arbitrary Attribute

noncomputable def toRA (dbi : DatabaseInstance) [Fintype ↑(adomRs dbi.schema)] [Fintype ↑(adomAtts dbi.schema)] : fol.BoundedFormula Attribute n → RA.Query
  | .falsum => .empty default
  | .equal t₁ t₂ => .s (TermtoAtt (adomAtts dbi.schema).toFinset t₁) (TermtoAtt (adomAtts dbi.schema).toFinset t₂) (adom dbi)
  | .rel (.R dbs rn) ts => .R rn
  | .imp f₁ ⊥ => .d (adom dbi) (toRA dbi f₁)                      --  p → ⊥  = ¬p
  | .imp (.not f₁) f₂ => .u (toRA dbi f₁) (toRA dbi f₂)           -- ¬p → q  =  p ∨ q
  | .imp f₁ f₂ => .u (.d (adom dbi) (toRA dbi f₁)) (toRA dbi f₂)  --  p → q  = ¬p ∨ q
  | .all sf => .p (sf.freeVarFinset) (toRA dbi sf)
