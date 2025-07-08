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

def ArityToTuple {dbi: DatabaseInstance} {rn : RelationName} (va : Fin (dbi.schema rn).card → Part Value) : Tuple :=
  λ att => (((dbi.schema rn).index? att).map va).getD Part.none

@[simp]
theorem arityToTuple_dom {att} {rn : RelationName} {dbi : DatabaseInstance} {va : Fin (dbi.schema rn).card → Part Value}
  (h: ArityToTuple va ∈ (dbi.relations rn).tuples)
  : (ArityToTuple va att).Dom ↔ att ∈ dbi.schema rn := by
    simp_all [DatabaseInstance.validSchema]
    have h2 := RelationInstance.validSchema (dbi.relations rn) (ArityToTuple va) h
    exact Iff.symm (Eq.to_iff (congrFun (id (Eq.symm h2)) att))

@[simp]
theorem arityToTuple_def {dbi: DatabaseInstance} {rn : RelationName} {i : Fin (Finset.card (dbi.schema rn))} {va : Fin (dbi.schema rn).card → Part Value}
  : ArityToTuple va ((dbi.schema rn).fromIndex i) = va i
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
            simp_all only [Fin.coe_cast, Fin.eta]
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
      (dbi : DatabaseInstance)     →                      -- Every database instance
      (rn : RelationName)          →                      -- Every relation (and every arity)
      (va : Fin (dbi.schema rn).card → Part Value) →      -- Every value assignment (for this arity)
        ArityToTuple va ∈ (dbi.relations rn).tuples  -- Iff this value assignment corresponds with a tuple in the relation instance
          ↔ RelMap (.R dbi rn) va                         -- Then the RelationMap contains the relation for this value assignment
