import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import RelationalAlgebra.RelationalModel
import Mathlib.Data.PFun
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic

-- Operations for BoundedFormula
-- AND: ⊓
-- OR: ⊔
-- NOT: ∼
-- IMP: ⟹
-- BIIMP: ⇔

variable {α : Type*}

namespace FirstOrder

open FirstOrder RM

-- RM modifications and example
namespace RM
-- Add ordering
instance Attribute.instLe : IsTrans Attribute (.≤.) where
  trans {_ _ _: Attribute} := String.le_trans

instance Attribute.instAntisymm : IsAntisymm Attribute (.≤.) where
  antisymm {_ _: Attribute} := String.le_antisymm

instance Attribute.instTotal : IsTotal Attribute (.≤.) where
  total := String.le_total

def RelationSchema.ordering (rs : RelationSchema) : List Attribute
  := rs.sort (.≤.)

def foldIndex (needleAtt: Attribute) (carry: (ℕ × Bool)) (a: Attribute) : ℕ × Bool := if a = needleAtt ∨ carry.2 = true then (carry.1, true) else (carry.1 + 1, false)

def RelationSchema.index (rs : RelationSchema) (att: Attribute) : ℕ := (rs.ordering.foldl (foldIndex att) (0, false)).1

def RelationSchema.fromIndex (rs: RelationSchema) (i: Fin rs.card) : Attribute := rs.ordering.get ⟨i, by simp [RelationSchema.ordering]⟩

end RM

def tup1 : Tuple
  | "a1" => some 11
  | "a2" => some 12
  | _ => Part.none

def tup2 : Tuple
  | "a1" => some 21
  | "a2" => some 22
  | _ => Part.none

def tup3 : Tuple
  | "a1" => some 31
  | "a2" => some 32
  | _ => Part.none

def relS : RelationSchema := {"a1", "a2"}

def relI : RelationInstance := ⟨
  relS,
  {tup1, tup2, tup3},
  by
    simp [relS, tup1, tup2, tup3, PFun.Dom]
    aesop
⟩


/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : (ri: RelationInstance) → relations ri.schema.card

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
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, v]
  simp
  use Part.none
  simp [Term.liftAt, Fin.snoc, v]

-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ ri : RelationInstance,                          -- Every relation (and every arity)
      ∀ a : Fin ri.schema.card → Part Value,          -- Every value assignment (for this arity)
        (∃ t : Tuple,                                   -- Exists a tuple
          ∀ v : Fin ri.schema.card,                   -- Every column index (up to arity)
            a v = t (ri.schema.fromIndex v)                     -- The column index is some value
        )
          → RelMap (R ri) a                             -- Then the RelationMap contains the relation for this value assignment



-- Revise this, it should connect RI Attributes and fol variables
def RelationTermAssignment := (a: Attribute) → fol.Term (Attribute ⊕ Fin 0)

def a_t : RelationTermAssignment
  | "a1" => Term.var (Sum.inl "x")
  | "a2" => Term.var (Sum.inl "y")
  | _ => Term.var (Sum.inl "x")

def getRelationTerms : (ri: RelationInstance) → Fin ri.schema.card → fol.Term (Attribute ⊕ (Fin 0))
  | ri, n => a_t (ri.schema.fromIndex n)

-- Revise this, it should be generalized to be a type of BoundedFormula, instead of Formula
def BoundedRelation (ri : RelationInstance) : fol.Formula Attribute := Relations.boundedFormula (R ri) (getRelationTerms ri)



example [struc: folStruc] : (BoundedRelation relI).Realize v := by
  simp only [Formula.Realize, BoundedRelation, BoundedFormula.realize_rel, getRelationTerms, a_t]
  apply folStruc.RelMap_R relI
  . use tup2
    intro i
    simp_all [tup2, v]
    split
    next x heq => rfl
    next x heq => rfl
    next x x_1 x_2 =>
      simp_all only [imp_false]
      simp_all only [Term.realize_var, Sum.elim_inl, v]
      simp_all only [Part.coe_some, Part.some_ne_none]

      simp_all [relI, RM.RelationSchema.fromIndex]

      -- Solve the proof by using the decide for the ordering
      have relSOrdering : RM.RelationSchema.ordering relS = ["a1", "a2"] := by simp [relS]; native_decide
      simp [relSOrdering] at *
      -- sorry
      induction i with
      | mk val h =>
        simp_all only
        simp [relI, relS] at h
        induction val with
        | zero => aesop
        | succ n => aesop
