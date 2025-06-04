import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import RelationalAlgebra.RelationalModel
import Mathlib.Data.PFun

-- Operations for BoundedFormula
-- AND: ⊓
-- OR: ⊔
-- NOT: ∼
-- IMP: ⟹
-- BIIMP: ⇔

variable {α : Type*}

namespace FirstOrder

open FirstOrder RM

/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : relations 1
  deriving DecidableEq

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving IsRelational


open relations Language


-- Terms are still unclear, figure this concept out further
def x : fol.Term (Attribute ⊕ Fin 0) := Term.var (Sum.inl "x")
def y : fol.Term (Attribute ⊕ Fin 0) := Term.var (Sum.inl "y")
def z : fol.Term (Attribute ⊕ Fin 1) := Term.var (Sum.inr 0)


-- Explore formula concepts
def n_xy : fol.BoundedFormula Attribute 0 := ∼(x =' y) ⟹ ⊤

def ex_n_xy_or_yz : fol.Formula Attribute := .ex ((n_xy.liftAt 1 0) ⊔ (y.liftAt 1 0) =' z)

def ex_n_xy_and_yz : fol.Formula Attribute := .ex ((n_xy.liftAt 1 0) ⊓ (y.liftAt 1 0) =' z)

def all_xz_or_yz : fol.Formula Attribute := .ex ((y.liftAt 1 0) =' z ⟹ ∼((x.liftAt 1 0) =' z))

def v : Attribute →. Value
  | "x" => "v1"
  | "y" => "v2"
  | _ => Part.none

example [struc: fol.Structure (Part Value)] : ex_n_xy_or_yz.Realize v := by
  simp only [Formula.Realize, ex_n_xy_or_yz, n_xy, x, y, z, v, BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_sup, BoundedFormula.realize_liftAt_one_self,
    BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true, true_or, exists_const]

example [struc: fol.Structure (Part Value)] : ex_n_xy_and_yz.Realize v := by
  simp only [Formula.Realize, ex_n_xy_and_yz, n_xy, x, y, z, v, BoundedFormula.realize_ex]
  use "v2"
  simp
  rfl

example [struc: fol.Structure (Part Value)] : all_xz_or_yz.Realize v := by
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, v]
  simp
  use "v1"
  simp [Term.liftAt, Fin.snoc, v]


-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R {n} :      -- Add proof to RelMap for each Relation in the Language
      ∀ rel : fol.Relations n,              -- Every relation (and every arity)
      ∀ a : Fin n → Part Value,             -- Every value assignment (for this arity)
        (∀ v : Fin n,                       -- Every column index (up to arity)
          a v = Part.some "v1"              -- The column index is some value
        )
          → RelMap rel a                    -- Then the RelationMap contains the relation for this value assignment

def getRelationTerms {n l : ℕ} : fol.Relations n → Fin n → fol.Term (Attribute ⊕ (Fin l))
  | _, _ => Term.var (Sum.inl "x")

def R_x : fol.Formula Attribute := Relations.boundedFormula R (getRelationTerms R)

example [struc: folStruc] : R_x.Realize v := by
  simp only [Formula.Realize, R_x, BoundedFormula.realize_rel, getRelationTerms]
  simp only [Term.realize_var, Sum.elim_inl]
  apply folStruc.RelMap_R R (fun _ ↦ v "x") (fun _ ↦ rfl)
