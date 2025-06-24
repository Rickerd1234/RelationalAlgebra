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
  | R : (rn: RelationName) → (rs: RelationSchema) → relations rs.card

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving Language.IsRelational


open Language

-- Define variable indexing types
abbrev Variable := String
abbrev VariableTerm (n: ℕ) := fol.Term (Variable ⊕ Fin n)

def outVar {n: ℕ} (v: Variable) : VariableTerm n := Term.var (Sum.inl v)
def inVar {n: ℕ} (i: Fin n) : VariableTerm n := Term.var (Sum.inr i)


def assignmentInRelation {ri: RelationInstance} (a : Fin ri.schema.card → Part Value) : Prop :=
    -- || Instead of this ∃, a unique mapping from a to t could be used?
  (∃ t : Tuple,                                   -- Exists a tuple
    t ∈ ri.tuples ∧                               -- Make sure t is contained in the set of tuples
    ∀ i : Fin ri.schema.card,                     -- Every column index (up to arity)
      a i = t (RelationSchema.fromIndex i)        -- The column index is some value
  )

-- Explore relation concepts
class folStruc (dbi : DatabaseInstance) extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ rn : RelationName,                                    -- Every relation (and every arity)
      ∀ a : Fin (dbi.relations rn).schema.card → Part Value,  -- Every value assignment (for this arity)
        assignmentInRelation a                                -- If this value assignment is valid in the relation instance
          → RelMap (.R rn (dbi.relations rn).schema) a        -- Then the RelationMap contains the relation for this value assignment


-- Convert RM.Attribute to FOL.Variable
-- @TODO: Think about whether databaseInstance should be part of this, since a Query should not require this
structure RelationTermRestriction (n: ℕ) where
  fn : Attribute →. VariableTerm n
  name : RelationName
  databaseInstance : DatabaseInstance
  validSchema : fn.Dom = databaseInstance.schema name

def RelationTermRestriction.schema {n: ℕ} (rtr : RelationTermRestriction n) := rtr.databaseInstance.schema rtr.name

theorem rtr_dom {n : ℕ} (rtr : RelationTermRestriction n) : ∀ i, (rtr.fn (rtr.schema.fromIndex i)).Dom := by
  intro i
  apply Part.dom_iff_mem.mpr
  apply (PFun.mem_dom rtr.fn (RelationSchema.fromIndex i)).mp
  simp [rtr.validSchema] at *

def getMap {n : ℕ} (rtr : RelationTermRestriction n) : Fin rtr.schema.card → VariableTerm n :=
  λ i => (rtr.fn (RelationSchema.fromIndex i)).get (rtr_dom rtr i)
