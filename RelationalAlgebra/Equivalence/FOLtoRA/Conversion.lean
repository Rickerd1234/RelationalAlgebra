import RelationalAlgebra.Equivalence.FOLtoRA.Adom

open FOL FirstOrder Language

def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula Attribute n :=
  q.toFormula.toPrenex

def toRA : fol.BoundedFormula Attribute n → RA.Query
  | .falsum => sorry
  | .equal t₁ t₂ => .s sorry sorry (sorry)
  | .rel (.R dbs rn) ts => .R rn
  | .imp f₁ ⊥ => .d sorry (toRA f₁)                 --  p → ⊥  = ¬p
  | .imp (.not f₁) f₂ => .u (toRA f₁) (toRA f₂)     -- ¬p → q  =  p ∨ q
  | .imp f₁ f₂ => .u (.d sorry (toRA f₁)) (toRA f₂) --  p → q  = ¬p ∨ q
  | .all sf => .p (sf.freeVarFinset) (toRA sf)
