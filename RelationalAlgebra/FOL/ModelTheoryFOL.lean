import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Ordering

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.PFun

namespace FOL

open FirstOrder RM

/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : (ri: RelationInstance) → relations ri.schema.card

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving Language.IsRelational


open Language

-- Define variable indexing types
abbrev Variable := String
abbrev VariableTerm (n: ℕ) := fol.Term (Variable ⊕ Fin n)

def var {n: ℕ} (v: Variable) : VariableTerm n := Term.var (Sum.inl v)
def free {n: ℕ} (i: Fin n) : VariableTerm n := Term.var (Sum.inr i)


-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ ri : RelationInstance,                          -- Every relation (and every arity)
      ∀ a : Fin ri.schema.card → Part Value,            -- Every value assignment (for this arity)
        (∃ t : Tuple,                                   -- Exists a tuple
          ∀ v : Fin ri.schema.card,                     -- Every column index (up to arity)
            a v = t (RelationSchema.fromIndex v)        -- The column index is some value
        )
          → RelMap (.R ri) a                            -- Then the RelationMap contains the relation for this value assignment


-- Convert RM.Attribute to FOL.Variable
def AttributeTermAssignment (n: ℕ) := Attribute →. VariableTerm n

structure RelationTermRestriction (n: ℕ) where
  fn : AttributeTermAssignment n
  inst : RelationInstance
  validSchema : fn.Dom = inst.schema

theorem rtr_dom {n : ℕ} (rtr : RelationTermRestriction n) : ∀ i, (rtr.fn (rtr.inst.schema.fromIndex i)).Dom := by
  intro i
  apply Part.dom_iff_mem.mpr
  apply (PFun.mem_dom rtr.fn (RelationSchema.fromIndex i)).mp
  simp [rtr.validSchema] at *

def getMap {n : ℕ} (rtr : RelationTermRestriction n) : Fin rtr.inst.schema.card → VariableTerm n :=
  λ i => (rtr.fn (RelationSchema.fromIndex i)).get (rtr_dom rtr i)

def BoundedRelation {n : ℕ} (rtr : RelationTermRestriction n) : fol.BoundedFormula Variable n :=
  Relations.boundedFormula (.R rtr.inst) (getMap rtr)
