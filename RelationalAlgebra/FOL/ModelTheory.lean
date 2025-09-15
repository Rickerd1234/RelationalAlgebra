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
  | R : (dbs: DatabaseSchema) → (rn: RelationName) → relations (dbs rn).card

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving Language.IsRelational

def fol.Rel (dbs: DatabaseSchema) (rn: RelationName) : Language.fol.Relations (dbs rn).card :=
  relations.R dbs rn

open Language

-- Define variable indexing types

def ArityToTuple {dbs: DatabaseSchema} {rn : RelationName} (va : Fin (dbs rn).card → Part Value) : Tuple :=
  λ att => dite (att ∈ dbs rn) (λ h => va ((dbs rn).index h)) (λ _ => Part.none)

theorem ArityToTuple.def_dite {dbs : DatabaseSchema} (va : Fin (dbs rn).card → Part Value) :
  ArityToTuple va = λ a => dite (a ∈ dbs rn) (λ h => va ((dbs rn).index h)) (λ _ => Part.none) := by
    rfl

theorem ArityToTuple.def_fromIndex {dbs : DatabaseSchema} (t : Tuple) (h : t.Dom ⊆ dbs rn) :
  ArityToTuple (fun i ↦ t ((dbs rn).fromIndex i)) = t := by
    simp_all [ArityToTuple.def_dite]
    ext a v
    apply Iff.intro
    · intro a_1
      split at a_1
      next h_1 => simp_all only
      next h_1 => simp_all only [Part.not_mem_none]
    · intro a_1
      split
      next h_1 => simp_all only
      next h_1 =>
        simp_all only [Part.not_mem_none]
        have z : a ∈ t.Dom := by apply Part.dom_iff_mem.mpr; use v
        exact h_1 (h z)

@[simp]
theorem arityToTuple_dom {att} {rn : RelationName} {dbi : DatabaseInstance} {va : Fin (dbi.schema rn).card → Part Value}
  (h: ArityToTuple va ∈ (dbi.relations rn).tuples)
  : (ArityToTuple va att).Dom ↔ att ∈ dbi.schema rn := by
    have h2 := RelationInstance.validSchema (dbi.relations rn) (ArityToTuple va) h
    simp_all [DatabaseInstance.validSchema]
    exact Iff.symm (Eq.to_iff (congrFun (id (Eq.symm h2)) att))

@[simp]
theorem arityToTuple_def {dbs: DatabaseSchema} {rn : RelationName} {i : Fin (Finset.card (dbs rn))} {va : Fin (dbs rn).card → Part Value}
  : ArityToTuple va ((dbs rn).fromIndex i) = va i
    := by simp [ArityToTuple]

-- Explore relation concepts
class folStruc (dbi : DatabaseInstance) extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      (rn : RelationName)          →                      -- Every relation (and every arity)
      (va : Fin (dbi.schema rn).card → Part Value) →             -- Every value assignment (for this arity)

        RelMap (.R dbi.schema rn) va ↔                             -- Then the RelationMap contains the relation for this value assignment
        (                                                   -- @TODO, Update the comments  - Iff this value assignment corresponds with a tuple in the relation instance
          ArityToTuple va ∈ (dbi.relations rn).tuples
        )

@[simp]
theorem folStruc_apply_RelMap (dbi : DatabaseInstance) [folStruc dbi] {rn va} :
  Structure.RelMap (fol.Rel dbi.schema rn) va ↔ ArityToTuple va ∈ (dbi.relations rn).tuples
    := (folStruc.RelMap_R rn va)

@[simp]
theorem fol_empty_fun {n} (_f : fol.Functions n) : False := by
  exact Aesop.BuiltinRules.empty_false _f

theorem Term.cases {n} (t : fol.Term (Attribute ⊕ (Fin n))) : ∃k, t = var k := by
  cases t with | var k => use k | func _f _ => exact False.elim (fol_empty_fun _f)
