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
  | R : (rs: RelationSchema) → relations rs.card

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


def assignmentInRelation {ri: RelationInstance} (a : Fin ri.schema.card → Part Value) : Prop :=
    -- || Instead of this ∃, a unique mapping from a to t could be used?
  (∃ t : Tuple,                                   -- Exists a tuple
    t ∈ ri.tuples ∧                               -- Make sure t is contained in the set of tuples
    ∀ i : Fin ri.schema.card,                     -- Every column index (up to arity)
      a i = t (RelationSchema.fromIndex i)        -- The column index is some value
  )

-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ ri : RelationInstance,                          -- Every relation (and every arity)
      ∀ a : Fin ri.schema.card → Part Value,            -- Every value assignment (for this arity)
        assignmentInRelation a                          -- If this value assignment is valid in the relation instance
          → RelMap (.R ri.schema) a                     -- Then the RelationMap contains the relation for this value assignment


-- Convert RM.Attribute to FOL.Variable
structure RelationTermRestriction (n: ℕ) where
  fn : Attribute →. VariableTerm n
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
  Relations.boundedFormula (.R rtr.inst.schema) (getMap rtr)
