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

namespace FirstOrder

open FirstOrder RM

-- RM modifications and example
namespace RM
-- Add ordering
instance Attribute.instLe : IsTrans Attribute (.≤.) where
  trans {_ _ _: Attribute} := Nat.le_trans

instance Attribute.instAntisymm : IsAntisymm Attribute (.≤.) where
  antisymm {_ _: Attribute} := Nat.le_antisymm

instance Attribute.instTotal : IsTotal Attribute (.≤.) where
  total := Nat.le_total

def RelationSchema.ordering (rs : RelationSchema) : List Attribute
  := rs.sort (.≤.)

def foldIndex (needleAtt: Attribute) (carry: (ℕ × Bool)) (a: Attribute) : ℕ × Bool := if a = needleAtt ∨ carry.2 = true then (carry.1, true) else (carry.1 + 1, false)

def RelationSchema.index (rs : RelationSchema) (att: Attribute) : ℕ := (rs.ordering.foldl (foldIndex att) (0, false)).1

def RelationSchema.fromIndex (rs: RelationSchema) (i: Fin rs.card) : Attribute := rs.ordering.get ⟨i, by simp [RelationSchema.ordering]⟩

end RM

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


/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : (ri: RelationInstance) → relations ri.schema.card

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving IsRelational


open relations Language

-- Define variable indexing types
abbrev Variable := String
abbrev VariableTerm (n: ℕ) := fol.Term (Variable ⊕ Fin n)


-- Terms are still unclear, figure this concept out further
def x : VariableTerm 0 := Term.var (Sum.inl "x")
def y : VariableTerm 0 := Term.var (Sum.inl "y")
def z : VariableTerm 1 := Term.var (Sum.inr 0)


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
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, v]
  simp
  use Part.none
  simp [Term.liftAt, Fin.snoc, v]

-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ ri : RelationInstance,                          -- Every relation (and every arity)
      ∀ a : Fin ri.schema.card → Part Value,            -- Every value assignment (for this arity)
        (∃ t : Tuple,                                   -- Exists a tuple
          ∀ v : Fin ri.schema.card,                     -- Every column index (up to arity)
            a v = t (ri.schema.fromIndex v)             -- The column index is some value
        )
          → RelMap (R ri) a                             -- Then the RelationMap contains the relation for this value assignment



-- Revise this, it should connect RI Attributes and fol variables
def RelationTermAssignment (n: ℕ) := (a: Attribute) → VariableTerm n

def a_t (n: ℕ) : RelationTermAssignment n
  | 0 => Term.var (Sum.inl "x")
  | 1 => Term.var (Sum.inl "y")
  | _ => Term.var (Sum.inl "_")

def getRelationTerms (n: ℕ) : (ri: RelationInstance) → Fin ri.schema.card → VariableTerm n
  | ri, i => a_t n (ri.schema.fromIndex i)

-- Revise this, it should be generalized to be a type of BoundedFormula, instead of Formula
def BoundedRelation (ri : RelationInstance) : fol.Formula Variable := Relations.boundedFormula (R ri) (getRelationTerms 0 ri)


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
