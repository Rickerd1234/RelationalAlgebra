import RelationalAlgebra.RelationalModel

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
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

@[simp]
theorem RelationSchema.ordering_mem (a : Attribute) (rs : RelationSchema) : a ∈ rs.ordering ↔ a ∈ rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_card (rs : RelationSchema) : rs.ordering.length = rs.card := by simp [ordering]

def RelationSchema.index? (rs : RelationSchema) (att : Attribute) : Option (Fin rs.card) :=
  (rs.ordering.finIdxOf? att).map (λ x : Fin (rs.ordering.length) => ⟨x, by simp [← RelationSchema.ordering_card]⟩)

@[simp]
theorem index_isSome {rs : RelationSchema} {att : Attribute} : (h : att ∈ rs) → (rs.index? att).isSome := by
  simp [← RelationSchema.ordering_mem, RelationSchema.index?]
  induction (RelationSchema.ordering rs) with
  | nil =>
    intro h
    simp_all only [List.not_mem_nil]
  | cons a as tail_ih =>
    intro h
    simp_all only [List.mem_cons, List.length_cons, List.finIdxOf?_cons, beq_iff_eq, Fin.zero_eta]
    cases h with
    | inl att_is_a => simp_all only [att_is_a, ↓reduceIte, Option.isSome_some]
    | inr h_2 =>
      simp_all only [forall_const]
      split
      next h => simp_all only [h, Option.isSome_some]
      next h => simp_all only [Option.isSome_map']

def RelationSchema.index {rs : RelationSchema} {att : Attribute} (h : att ∈ rs) : Fin rs.card :=
  (RelationSchema.index? rs att).get (index_isSome h)

@[simp]
theorem index_lt_card {rs : RelationSchema} {att : Attribute} : (h : att ∈ rs) → rs.index h < rs.card := by
  simp [RelationSchema.ordering_mem, RelationSchema.index, RelationSchema.index?]

def RelationSchema.fromIndex (rs : RelationSchema) (i : Fin rs.card) : Attribute := rs.ordering.get ⟨i, by simp [RelationSchema.ordering]⟩

@[simp]
theorem fromIndex_mem {rs : RelationSchema} : (i : Fin rs.card) → rs.fromIndex i ∈ rs := by
  intro i
  apply (RelationSchema.ordering_mem (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) rs)[i] rs).mp
  simp [RelationSchema.ordering]

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

def var {n: ℕ} (v: Variable) : VariableTerm n := Term.var (Sum.inl v)
def free {n: ℕ} (i: Fin n) : VariableTerm n := Term.var (Sum.inr i)

-- Terms are still unclear, figure this concept out further
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


-- Convert RM.Attribute to FOL.Variable
def AttributeTermAssignment (n: ℕ) := Attribute →. VariableTerm n

structure RelationTermRestriction (n: ℕ) where
  fn : AttributeTermAssignment n
  inst : RelationInstance
  validSchema : fn.Dom = inst.schema

theorem rtr_dom {n : ℕ} (rtr : RelationTermRestriction n) : ∀ i, (rtr.fn (rtr.inst.schema.fromIndex i)).Dom := by
  intro i
  apply Part.dom_iff_mem.mpr
  apply (PFun.mem_dom rtr.fn (RM.RelationSchema.fromIndex rtr.inst.schema i)).mp
  simp [rtr.validSchema] at *

def getMap {n : ℕ} (rtr : RelationTermRestriction n) : Fin rtr.inst.schema.card → VariableTerm n :=
  λ i => (rtr.fn (rtr.inst.schema.fromIndex i)).get (rtr_dom rtr i)

def BoundedRelation {n : ℕ} (rtr : RelationTermRestriction n) : fol.BoundedFormula Variable n := Relations.boundedFormula (R rtr.inst) (getMap rtr)

-- Relation with variables
def F : fol.Formula Variable := BoundedRelation ⟨
λ a => match a with
  | 0 => .some (var "x")
  | 1 => .some (var "y")
  | _ => .none,
  relI,
  by simp [relI, relS, PFun.Dom]; aesop
⟩

example [struc: folStruc] : F.Realize v := by
  simp only [Formula.Realize, F, BoundedRelation, BoundedFormula.realize_rel]
  apply folStruc.RelMap_R relI
  use tup2
  intro i
  simp only [tup2, v, Part.coe_some]
  split
  all_goals simp_all [getMap]; try rfl
  next x x_1 x_2 =>
    have z := RM.fromIndex_mem i
    simp_all [relI, relS]

-- Relation with a free variable
def rtr_G : RelationTermRestriction 1 := ⟨
  λ a => match a with
    | 0 => .some (var "x")
    | 1 => .some (free 0)
    | _ => .none,
  relI,
  by simp [relI, relS, PFun.Dom]; aesop
⟩

def G : fol.Formula Variable := .ex (BoundedRelation rtr_G)
example [struc: folStruc] : G.Realize v := by
  simp [Formula.Realize, G, BoundedRelation, BoundedFormula.realize_rel]
  use .some 22
  apply folStruc.RelMap_R relI
  use tup2
  intro i
  simp_all only [tup2, Part.coe_some]
  split
  all_goals simp_all [rtr_G, getMap]; try rfl
  next x x_1 x_2 =>
    have z := RM.fromIndex_mem i
    simp_all [relI, relS]

-- Relation with two free variables
def rtr_H : RelationTermRestriction 2 := ⟨
  λ a => match a with
    | 0 => .some (free 1)
    | 1 => .some (free 0)
    | _ => .none,
  relI,
  by simp [relI, relS, PFun.Dom]; aesop
⟩

def H : fol.Formula Variable := .ex (.ex (BoundedRelation rtr_H))
example [struc: folStruc] : H.Realize v := by
  simp [Formula.Realize, H, BoundedRelation, BoundedFormula.realize_rel]
  use .some 22
  use .some 21
  apply folStruc.RelMap_R relI
  use tup2
  intro i
  simp_all only [tup2, Part.coe_some]
  split
  all_goals simp_all [rtr_H, getMap]; try rfl
  next x x_1 x_2 =>
    have z := RM.fromIndex_mem i
    simp_all [relI, relS]
