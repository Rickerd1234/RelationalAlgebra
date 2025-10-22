import RelationalAlgebra.RelationalModel
import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.Util.PFunFinRan

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.PFun
import Mathlib.Data.Finset.PImage

namespace FOL

open RM

-- (Partial) Tuple to complete function
section TupleToFun

variable {t t' : Tuple} {rs rs' : RelationSchema}

@[simp]
instance fintype_dom (h : t.Dom = rs) : Fintype ↑t.Dom := by
  apply Fintype.ofFinset rs (Set.ext_iff.mp h.symm)

@[simp]
instance decidable_dom (h : t.Dom = rs) : ∀a, Decidable (t a).Dom := by
  intro a
  simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
  exact Finset.decidableMem a rs

@[simp]
noncomputable def TupleToFun (h : t.Dom = rs) : Attribute → Value :=
  by
    haveI := decidable_dom h
    exact λ a => (t a).getOrElse (Classical.arbitrary Value)

@[simp]
theorem TupleToFun.tuple_eq (h : t.Dom = rs) (h' : t'.Dom = rs') (h'' : t = t') :
  TupleToFun h = TupleToFun h' := by
    ext a
    simp_all only [TupleToFun, Part.getOrElse]
    aesop

@[simp]
theorem TupleToFun.tule_eq_self (h : t.Dom = rs) (h' : t.Dom = rs') :
  TupleToFun h = TupleToFun h' := tuple_eq h h' rfl

@[simp]
theorem TupleToFun.tuple_eq_ext {h : t.Dom = rs} {h' : t.Dom = rs'} (h'' : t a = t b) :
  TupleToFun h a = TupleToFun h' b := by
    simp
    by_cases (t a).Dom
    all_goals simp_all [Part.getOrElse]

@[simp]
theorem TupleToFun.tuple_eq_att_ext {h : t.Dom = rs} {h' : t'.Dom = rs'} (h'' : t a = t' a) :
  TupleToFun h a = TupleToFun h' a := by
    by_cases (t a).Dom
    all_goals simp_all [Part.getOrElse]

end TupleToFun


-- Define variable indexing types
section ArityToTuple

def ArityToTuple {rs: RelationSchema} (va : Fin rs.card → Value) : Tuple :=
  λ att => dite (att ∈ rs) (λ h => va (rs.index h)) (λ _ => Part.none)

@[simp]
theorem ArityToTuple.def_dite {rs : RelationSchema} (va : Fin rs.card → Value) :
  ArityToTuple va = λ att => dite (att ∈ rs) (λ h => .some (va (rs.index h))) (λ _ => Part.none) := by
    rfl

theorem ArityToTuple.def_fromIndex {rs : RelationSchema} {t : Tuple} (h : t.Dom = ↑rs) :
  ArityToTuple (fun i : Fin rs.card ↦ (TupleToFun h (RM.RelationSchema.fromIndex i))) = t := by
    simp
    ext a v
    have : (t a).Dom ↔ a ∈ rs := by exact Iff.symm (Eq.to_iff (congrFun (id (Eq.symm h)) a))
    split
    all_goals simp_all [Part.getOrElse, Part.dom_iff_mem]

end ArityToTuple


-- Define relation concept for FOL
section folStruc

open FirstOrder

/-- The type of Relations in FOL -/
inductive relations : ℕ → Type
  | R : (dbs: DatabaseSchema) → (rn: RelationName) → relations (dbs rn).card

/-- The language of fol contains the relations -/
def Language.fol : Language :=
  { Functions := fun _ => Empty
    Relations := relations }
  deriving Language.IsRelational

@[simp]
def fol.Rel (dbs: DatabaseSchema) (rn: RelationName) : Language.fol.Relations (dbs rn).card :=
  relations.R dbs rn


open Language

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

end folStruc
