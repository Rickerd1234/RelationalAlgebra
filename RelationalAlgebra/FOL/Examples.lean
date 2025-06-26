import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Util
import RelationalAlgebra.FOL.Query

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

def dbI : DatabaseInstance := ⟨
  λ x => match x with
  | "R1" => relS
  | _ => ∅,
  λ x => match x with
  | "R1" => relI
  | _ => ∅r ∅,
  by
    intro rel
    simp_all only [RelationInstance.empty]
    split
    next x => rfl
    next x x_1 => simp_all only [imp_false]
⟩

open FOL Language

def x : VariableTerm 0 := outVar "x"
def y : VariableTerm 0 := outVar "y"
def z : VariableTerm 1 := inVar 0

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
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, v, outVar, inVar]
  simp
  use Part.none
  simp [Term.liftAt, Fin.snoc, v]


-- Relation with variables
def F : Query := BoundedQuery.R ⟨
  λ a => match a with
  | 0 => .some (outVar "x")
  | 1 => .some (outVar "y")
  | _ => .none,
  "R1",
  dbI,
  (by simp [relS, PFun.Dom, dbI]; aesop)
⟩

example [struc: folStruc] : F.Realize dbI v := by
  simp only [Query.Realize, F]
  apply folStruc.RelMap_R dbI "R1"
  use tup2
  apply And.intro
  · simp [dbI, relI]
  · intro i
    simp only [tup2, v, Part.coe_some]
    split
    all_goals simp_all [getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [dbI, relI, relS]

-- Relation with a free variable
def rtr_G : RelationTermRestriction 1 := ⟨
  λ a => match a with
    | 0 => .some (outVar "x")
    | 1 => .some (inVar 0)
    | _ => .none,
  "R1",
  dbI,
  (by simp [relS, PFun.Dom, dbI]; aesop)
⟩

def G : Query := .ex (.R rtr_G)
example [struc: folStruc] : G.Realize dbI v := by
  simp [Query.Realize, BoundedQuery.Realize, BoundedQuery.toFormula, G]
  use .some 22
  apply folStruc.RelMap_R dbI "R1"
  use tup2
  apply And.intro
  · simp [dbI, relI]
  · intro i
    simp_all only [tup2, Part.coe_some]
    split
    all_goals simp_all [rtr_G, getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [dbI, relI, relS]

-- Relation with two free variables
def rtr_H : RelationTermRestriction 2 := ⟨
  λ a => match a with
    | 0 => .some (inVar 1)
    | 1 => .some (inVar 0)
    | _ => .none,
  "R1",
  dbI,
  (by simp [relS, PFun.Dom, dbI]; aesop)
⟩

def H : Query := .ex (.ex (.R rtr_H))
example [struc: folStruc] : H.Realize dbI v := by
  simp [Query.Realize, BoundedQuery.Realize, BoundedQuery.toFormula, H]
  use .some 22
  use .some 21
  apply folStruc.RelMap_R dbI "R1"
  use tup2
  apply And.intro
  · simp [dbI, relI]
  · intro i
    simp_all only [tup2, Part.coe_some]
    split
    all_goals simp_all [rtr_H, getMap]; try rfl
    next x x_1 x_2 =>
      have z := RelationSchema.fromIndex_mem i
      simp_all [dbI, relI, relS]

def t : EvaluableQuery (dbI) :=
  ⟨
    G,
    {1},
    λ x => match x with
    | 1 => "x"
    | _ => .none,
    by
      simp [variablesInQuery, G, rtr_G, variablesInRTR, Language.var, VariableTerm.outVar?, RelationTermRestriction.vars, PFun.ran]
      ext
      simp_all only [Set.mem_setOf_eq, Fin.isValue]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        split at h
        next x_1 =>
          simp_all only [Part.mem_some_iff, Fin.isValue]
          subst h
          use outVar "x"
          simp [outVar]
          use 0
          simp
        next x_1 x_2 => simp_all only [imp_false, Part.not_mem_none]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := left
        split at right
        next x_1 x_2 =>
          split at h
          next x_3 =>
            simp_all only [Sum.getLeft?_eq_some_iff, Part.mem_some_iff]
            subst right
            use 1
            simp_all [outVar]
          next x_3 =>
            simp_all only [Sum.getLeft?_eq_some_iff, Fin.isValue, Part.mem_some_iff]
            subst right
            use 1
            simp_all [inVar]
          next x_3 x_4 x_5 => simp_all only [Sum.getLeft?_eq_some_iff, imp_false, Part.not_mem_none]
        next x_1 x_2 =>
          split at h
          next x_3 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
          next x_3 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
          next x_3 x_4 x_5 => simp_all only [imp_false, Sum.forall, reduceCtorEq],
    by aesop
  ⟩
