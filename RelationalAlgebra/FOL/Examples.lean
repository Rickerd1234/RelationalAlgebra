import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.ModelTheoryFOL

-- Operations for BoundedFormula
-- AND: ⊓
-- OR: ⊔
-- NOT: ∼
-- IMP: ⟹
-- BIIMP: ⇔
-- EX: .ex
-- ALL: .all


namespace FOL

open FirstOrder RM

def tup1 : Tuple
  | 0 => some 11
  | 1 => some 12
  | _ => Part.none

def tup2 : Tuple
  | 0 => some 21
  | 1 => some 22
  | _ => Part.none

def tup3 : Tuple
  | 0 => some 31
  | 1 => some 32
  | _ => Part.none

def relS : RelationSchema := {0, 1}

def relI : RelationInstance := ⟨
  relS,
  {tup1, tup2, tup3},
  by
    simp [relS, tup1, tup2, tup3, PFun.Dom]
    aesop
⟩

open FOL Language

def x : VariableTerm 0 := var "x"
def y : VariableTerm 0 := var "y"
def z : VariableTerm 1 := free 0

-- Explore formula concepts
def n_xy : fol.BoundedFormula Variable 0 := ∼(x =' y) ⟹ ⊤

def ex_n_xy_or_yz : fol.Formula Variable := .ex ((n_xy.liftAt 1 0) ⊔ (y.liftAt 1 0) =' z)

def ex_n_xy_and_yz : fol.Formula Variable := .ex ((n_xy.liftAt 1 0) ⊓ (y.liftAt 1 0) =' z)

def all_xz_or_yz : fol.Formula Variable := .ex ((y.liftAt 1 0) =' z ⟹ ∼((x.liftAt 1 0) =' z))

def v : Variable →. Value
  | "x" => some 21
  | "y" => some 22
  | _ => Part.none

example [struc: fol.Structure (Part Value)] : ex_n_xy_or_yz.Realize v := by
  simp only [Formula.Realize, ex_n_xy_or_yz, n_xy, x, y, z, v, BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_sup, BoundedFormula.realize_liftAt_one_self,
    BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true, true_or, exists_const]

example [struc: fol.Structure (Part Value)] : ex_n_xy_and_yz.Realize v := by
  simp only [Formula.Realize, ex_n_xy_and_yz, n_xy, x, y, z, v, BoundedFormula.realize_ex]
  use some 22
  simp
  rfl

example [struc: fol.Structure (Part Value)] : all_xz_or_yz.Realize v := by
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, v, var, free]
  simp
  use Part.none
  simp [Term.liftAt, Fin.snoc, v]


-- Relation with variables
def F : fol.Formula Variable := BoundedRelation ⟨
λ a => match a with
  | 0 => .some (var "x")
  | 1 => .some (var "y")
  | _ => .none,
  relS,
  by simp [relS, PFun.Dom]; aesop
⟩

example [struc: folStruc] : F.Realize v := by
  simp only [Formula.Realize, F, BoundedRelation, BoundedFormula.realize_rel]
  apply folStruc.RelMap_R relI
  use tup2
  apply And.intro
  · simp [relI]
  · intro i
    simp only [tup2, v, Part.coe_some]
    split
    all_goals simp_all [getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [relI, relS]

-- Relation with a free variable
def rtr_G : RelationTermRestriction 1 := ⟨
  λ a => match a with
    | 0 => .some (var "x")
    | 1 => .some (free 0)
    | _ => .none,
  relS,
  by simp [relS, PFun.Dom]; aesop
⟩

def G : fol.Formula Variable := .ex (BoundedRelation rtr_G)
example [struc: folStruc] : G.Realize v := by
  simp [Formula.Realize, G, BoundedRelation, BoundedFormula.realize_rel]
  use .some 22
  apply folStruc.RelMap_R relI
  use tup2
  apply And.intro
  · simp [relI]
  · intro i
    simp_all only [tup2, Part.coe_some]
    split
    all_goals simp_all [rtr_G, getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [relI, relS]

-- Relation with two free variables
def rtr_H : RelationTermRestriction 2 := ⟨
  λ a => match a with
    | 0 => .some (free 1)
    | 1 => .some (free 0)
    | _ => .none,
  relS,
  by simp [relS, PFun.Dom]; aesop
⟩

def H : fol.Formula Variable := .ex (.ex (BoundedRelation rtr_H))
example [struc: folStruc] : H.Realize v := by
  simp [Formula.Realize, H, BoundedRelation, BoundedFormula.realize_rel]
  use .some 22
  use .some 21
  apply folStruc.RelMap_R relI
  use tup2
  apply And.intro
  · simp [relI]
  · intro i
    simp_all only [tup2, Part.coe_some]
    split
    all_goals simp_all [rtr_H, getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [relI, relS]
