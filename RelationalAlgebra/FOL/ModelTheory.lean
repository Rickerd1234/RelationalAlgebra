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
  λ att => (((dbs rn).index? att).map va).getD Part.none

theorem ArityToTuple.def_dite {dbs : DatabaseSchema} (va : Fin (dbs rn).card → Part Value) :
  ArityToTuple va a = dite (a ∈ dbs rn) (λ h => va ((dbs rn).index h)) (λ _ => Part.none) := by
    simp_all [ArityToTuple]
    split
    . rename_i h
      rw [← RelationSchema.index?_isSome, RelationSchema.index?_isSome_eq_iff] at h
      simp [RelationSchema.index]
      obtain ⟨w, h⟩ := h
      simp [h]
    . rename_i h
      rw [← RelationSchema.index?_none] at h
      simp [h]


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
    := by
      simp_all [ArityToTuple, RelationSchema.index?, Option.map, RelationSchema.ordering, Option.getD, RelationSchema.fromIndex]
      split
      next opt x heq =>
        split at heq
        next opt_1 x_1 heq_1 =>
          split at heq_1
          next opt_2 x_2
            heq_2 =>
            simp_all only [Option.some.injEq, List.finIdxOf?_eq_some_iff, Fin.getElem_fin]
            subst heq heq_1
            obtain ⟨left, right⟩ := heq_2
            -- Patch required for the aesop strategy used before
            have z : x_2 = i.cast (by aesop) := by
              simp_all [Fin.cast, Finset.length_sort];
              refine (List.Nodup.get_inj_iff ?_).mp left
              simp_all only [Finset.sort_nodup]
            subst z
            simp_all only [Fin.coe_cast, Fin.cast_trans, Fin.cast_eq_self]
          next opt_2 heq_2 =>
            simp_all only [Option.some.injEq, List.finIdxOf?_eq_none_iff, List.getElem_mem, not_true_eq_false]
        next opt_1 heq_1 =>
          split at heq_1
          next opt_2 x_1 heq_2 => simp_all only [reduceCtorEq]
          next opt_2 heq_2 => simp_all only [reduceCtorEq]
      next opt heq =>
        split at heq
        next opt_1 x heq_1 =>
          split at heq_1
          next opt_2 x_1 heq_2 => simp_all only [reduceCtorEq]
          next opt_2 heq_2 => simp_all only [reduceCtorEq]
        next opt_1 heq_1 =>
          split at heq_1
          next opt_2 x heq_2 => simp_all only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, reduceCtorEq]
          next opt_2 heq_2 => simp_all only [List.finIdxOf?_eq_none_iff, List.getElem_mem, not_true_eq_false]

-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      (dbs : DatabaseSchema)     →                        -- Every database schema
      (rn : RelationName)          →                      -- Every relation (and every arity)
      (va : Fin (dbs rn).card → Part Value) →             -- Every value assignment (for this arity)

        RelMap (.R dbs rn) va ↔                             -- Then the RelationMap contains the relation for this value assignment
        (                                                   -- @TODO, Update the comments  - Iff this value assignment corresponds with a tuple in the relation instance
          ∃dbi : DatabaseInstance,
              dbi.schema = dbs ∧ ArityToTuple va ∈ (dbi.relations rn).tuples
        )

@[simp]
theorem folStruc_apply_RelMap [folStruc] {dbs} {rn va} :
  Structure.RelMap (fol.Rel dbs rn) va ↔ ∃dbi : DatabaseInstance, dbi.schema = dbs ∧ ArityToTuple va ∈ (dbi.relations rn).tuples
    := (folStruc.RelMap_R dbs rn va)

@[simp]
theorem folStruc_empty_fun {n} [folStruc] (_f : fol.Functions n) : False := by
  exact Aesop.BuiltinRules.empty_false _f

theorem Term.cases [folStruc] (t : fol.Term (Attribute ⊕ (Fin n))) : ∃k, t = var k := by
  cases t with | var k => use k | func _f _ => exact False.elim (folStruc_empty_fun _f)
