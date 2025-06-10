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

theorem RelationSchema.ordering_mem (a : Attribute) (rs : RelationSchema) : a ∈ rs ↔ a ∈ rs.ordering := by simp [ordering]

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


-- Generalize this part, such that it is more intuitive
def AttributeTermAssignment (n: ℕ) := Attribute →. VariableTerm n

-- Convert RM.Attribute to FOL.Variable
def a_t {n: ℕ} : AttributeTermAssignment n
  | 0 => .some (var "x")
  | 1 => .some (var "y")
  | _ => .none

structure RelationTermRestriction (n: ℕ) where
  fn : AttributeTermAssignment n
  inst : RelationInstance
  validSchema : fn.Dom = inst.schema

theorem i_schema_mem (schema : RelationSchema) (i : Fin schema.card) : schema.fromIndex i ∈ schema := by
  simp_all only [Fin.is_le', RM.RelationSchema.fromIndex, RM.RelationSchema.ordering,
    List.get_eq_getElem, RM.RelationSchema.ordering_mem, List.getElem_mem]

theorem atr_dom {n : ℕ} (atr : RelationTermRestriction n) : ∀ i, (atr.fn (atr.inst.schema.fromIndex i)).Dom := by
  intro i
  apply Part.dom_iff_mem.mpr
  apply (PFun.mem_dom atr.fn (RM.RelationSchema.fromIndex atr.inst.schema i)).mp
  simp [atr.validSchema] at *
  exact i_schema_mem atr.inst.schema i

def getMap {n : ℕ} (atr : RelationTermRestriction n) : Fin atr.inst.schema.card → VariableTerm n :=
  λ i => (atr.fn (atr.inst.schema.fromIndex i)).get (atr_dom atr i)

def BoundedRelation {n : ℕ} (atr : RelationTermRestriction n) : fol.BoundedFormula Variable n := Relations.boundedFormula (R atr.inst) (getMap atr)


def F : fol.Formula Variable := BoundedRelation ⟨a_t, relI, by simp [relI, relS, a_t, PFun.Dom]; aesop⟩

example [struc: folStruc] : F.Realize v := by
  simp only [Formula.Realize, F, BoundedRelation, BoundedFormula.realize_rel, getMap, a_t]
  apply folStruc.RelMap_R relI
  . use tup2
    intro i
    simp only [tup2, v, Part.coe_some]
    split
    next x heq => rfl
    next x heq => rfl
    next x x_1 x_2 =>
      simp_all only [imp_false]
      simp_all only [Term.realize_var, Sum.elim_inl, v]
      simp_all only [Part.coe_some, Part.some_ne_none]
      simp_all [relI, RM.RelationSchema.fromIndex]


def atr_G : RelationTermRestriction 1 := ⟨
  λ a => match a with
    | 0 => .some (var "x")
    | 1 => .some (free 0)
    | _ => .none,
  relI,
  by simp [relI, relS, PFun.Dom]; aesop
⟩

def G : fol.Formula Variable := .ex (BoundedRelation atr_G)
example [struc: folStruc] : G.Realize v := by
  simp [Formula.Realize, G, BoundedRelation, BoundedFormula.realize_rel, getMap, atr_G]
  use .some 22
  apply folStruc.RelMap_R relI
  use tup2
  intro i
  simp_all [tup2, v, atr_dom, Term.realize_var, getMap, atr_G, Term.realize_var]
