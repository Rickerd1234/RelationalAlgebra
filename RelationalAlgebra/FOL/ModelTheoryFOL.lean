import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.Util.PFunFinRan

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.PFun
import Mathlib.Data.Finset.PImage

namespace FOL

open FirstOrder RM

/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : (dbi: DatabaseInstance) → (rn: RelationName) → relations (dbi.schema rn).card

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


def assignmentInRelation {dbi: DatabaseInstance} {rn : RelationName} (a : Fin (dbi.schema rn).card → Part Value) : Prop :=
    -- @TODO: Instead of this ∃, a unique mapping from a to t could be used?
  (∃ t : Tuple,                                   -- Exists a tuple
    t ∈ (dbi.relations rn).tuples ∧               -- Make sure t is contained in the set of tuples
    ∀ i : Fin (dbi.schema rn).card,               -- Every column index (up to arity)
      a i = t (RelationSchema.fromIndex i)        -- The column index is some value
  )

-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      ∀ dbi : DatabaseInstance,                     -- Every database instance
      ∀ rn : RelationName,                          -- Every relation (and every arity)
      ∀ a : Fin (dbi.schema rn).card → Part Value,  -- Every value assignment (for this arity)
        assignmentInRelation a                      -- If this value assignment is valid in the relation instance
          → RelMap (.R dbi rn) a                    -- Then the RelationMap contains the relation for this value assignment


-- Convert RM.Attribute to FOL.Variable
structure RelationTermRestriction (n: ℕ) where
  inFn : Attribute →. VariableTerm n
  name : RelationName
  fintypeDom : Fintype inFn.Dom

instance {n : ℕ} (rtr : RelationTermRestriction n) : Fintype rtr.inFn.Dom := rtr.fintypeDom

def RelationTermRestriction.schema {n: ℕ} (rtr : RelationTermRestriction n) : RelationSchema := rtr.inFn.Dom.toFinset

def RelationTermRestriction.vars {n : ℕ} (rtr : RelationTermRestriction n) : Finset (VariableTerm n) := rtr.inFn.ran.toFinset

-- Bounded relation term restriction, used to bind a specific database instance and verify the schema
structure BoundedRelationTermRestriction (n : ℕ) extends RelationTermRestriction n where
  dbi : DatabaseInstance
  validSchema : inFn.Dom = dbi.schema name

@[simp]
theorem rtr_dom_is_schema {n : ℕ} (brtr : BoundedRelationTermRestriction n) : brtr.dbi.schema brtr.name = brtr.schema := by
  simp only [RelationTermRestriction.schema, brtr.validSchema, Finset.toFinset_coe]

theorem rtr_dom {n : ℕ} (brtr : BoundedRelationTermRestriction n) (i : Fin (brtr.dbi.schema brtr.name).card) : (brtr.inFn ((brtr.dbi.schema brtr.name).fromIndex i)).Dom := by
  apply Part.dom_iff_mem.mpr
  apply (PFun.mem_dom brtr.inFn (RelationSchema.fromIndex i)).mp
  rw [brtr.validSchema]
  simp only [← rtr_dom_is_schema, Finset.mem_coe, RelationSchema.fromIndex_mem]

def getMap {n : ℕ} (brtr : BoundedRelationTermRestriction n) : Fin (brtr.dbi.schema brtr.name).card → VariableTerm n :=
  λ i => (brtr.inFn (RelationSchema.fromIndex i)).get (rtr_dom brtr i)
