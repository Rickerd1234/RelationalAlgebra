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

instance dec_dom {t : Tuple} {rs : RelationSchema} (h : t.Dom = rs) : Decidable (t a).Dom := by
  simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
  exact Finset.decidableMem a rs

def TupleToFun {rs : RelationSchema} {t : Tuple} (h : t.Dom = rs) : Attribute → Value :=
  by
    haveI : ∀ a, Decidable (t a).Dom := fun a => dec_dom h
    exact λ a => (t a).getOrElse default

@[simp]
theorem TupleToFun.def {rs : RelationSchema} {t : Tuple} (h : t.Dom = rs) [∀a, Decidable (t a).Dom] :
  TupleToFun h = λ a => (t a).getOrElse default := by rfl

def ArityToTuple {rs: RelationSchema} (va : Fin rs.card → Value) : Tuple :=
  λ att => dite (att ∈ rs) (λ h => va (rs.index h)) (λ _ => Part.none)

theorem ArityToTuple.def_dite {rs : RelationSchema} (va : Fin rs.card → Value) :
  ArityToTuple va = λ a => dite (a ∈ rs) (λ h => .some (va (rs.index h))) (λ _ => Part.none) := by
    rfl

theorem ArityToTuple.def_fromIndex {rs : RelationSchema} {t : Tuple} (h : t.Dom = ↑rs) :
  ArityToTuple (fun i : Fin rs.card ↦ (TupleToFun h (RM.RelationSchema.fromIndex i))) = t := by
    simp_all [ArityToTuple.def_dite]
    ext a v
    apply Iff.intro
    · intro a_1
      split at a_1
      next h_1 =>
        simp [Set.ext_iff, ← Part.dom_iff_mem] at h;
        simp_all [RelationSchema.fromIndex_index_eq, Part.getOrElse, Part.get_mem]
      next h_1 => simp_all only [Part.not_mem_none]
    · intro a_1
      split
      next h_1 =>
        simp_all [← Part.eq_some_iff, RelationSchema.fromIndex_index_eq]
      next h_1 =>
        simp_all only [Part.not_mem_none]
        have z : a ∈ t.Dom := by apply Part.dom_iff_mem.mpr; use v
        simp_all only [Finset.mem_coe]

@[simp]
theorem arityToTuple_dom {att} {rn : RelationName} {dbi : DatabaseInstance} {va : Fin (dbi.schema rn).card → Value}
  (h: ArityToTuple va ∈ (dbi.relations rn).tuples)
  : (ArityToTuple va att).Dom ↔ att ∈ dbi.schema rn := by
    have h2 := RelationInstance.validSchema (dbi.relations rn) (ArityToTuple va) h
    simp_all [DatabaseInstance.validSchema]
    exact Iff.symm (Eq.to_iff (congrFun (id (Eq.symm h2)) att))

@[simp]
theorem arityToTuple_def {dbs: DatabaseSchema} {rn : RelationName} {i : Fin (Finset.card (dbs rn))} {va : Fin (dbs rn).card → Value}
  : ArityToTuple va ((dbs rn).fromIndex i) = va i
    := by simp [ArityToTuple]

-- Explore relation concepts
class folStruc (dbi : DatabaseInstance) extends fol.Structure (Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      (rn : RelationName)          →                      -- Every relation (and every arity)
      (va : Fin (dbi.schema rn).card → Value) →             -- Every value assignment (for this arity)

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
