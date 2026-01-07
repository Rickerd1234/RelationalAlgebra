import RelationalAlgebra.Examples
import RelationalAlgebra.Util.RenameFunc
import RelationalAlgebra.FOL.Evaluate

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

open FOL Language

abbrev exFol := (fol exDatabase.schema)

def x : exFol.Term (String ⊕ Fin 0) := outVar "x"
def y : exFol.Term (String ⊕ Fin 0) := outVar "y"
def z : exFol.Term (String ⊕ Fin 1) := inVar 0

-- Explore formula concepts
def n_xy : exFol.BoundedFormula String 0 := ∼(x =' y)

def ex_n_xy_or_yz : exFol.Formula String := .ex ((n_xy.liftAt 1 0) ⊔ (y.liftAt 1 0) =' z)

def ex_n_xy_and_yz : exFol.Formula String := .ex ((n_xy.liftAt 1 0) ⊓ (y.liftAt 1 0) =' z)

def all_xz_or_yz : exFol.Formula String := .ex ((y.liftAt 1 0) =' z ⟹ ∼((x.liftAt 1 0) =' z))

@[simp]
def v' : String → String
  | "x" => "1"
  | "y" => "Anna"
  | _ => ""

example [struc: exFol.Structure (String)] : ex_n_xy_or_yz.Realize v' := by
  simp only [Formula.Realize, ex_n_xy_or_yz, n_xy, x, y, z, BoundedFormula.realize_ex]
  simp [BoundedFormula.realize_sup, BoundedFormula.realize_liftAt_one_self, true_or, exists_const]

example [struc: exFol.Structure (String)] : ex_n_xy_and_yz.Realize v' := by
  simp only [Formula.Realize, ex_n_xy_and_yz, n_xy, x, y, z, BoundedFormula.realize_ex]
  use "Anna"
  simp
  rfl

example [struc: exFol.Structure (String)] : all_xz_or_yz.Realize v' := by
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, outVar, inVar]
  simp
  use ""
  simp [Term.liftAt, Fin.snoc]


@[simp]
def v := PFun.res v' {"x", "y"}

-- Relation with variables
def F : Query exDatabase.schema := (.R "employee" [outVar "x", outVar "y"].get)

example (h : a ∈ exDatabase.schema "employee") :
  RelationSchema.index h < (exDatabase.schema "employee").card := by
    simp
    exact (RelationSchema.index h).isLt
