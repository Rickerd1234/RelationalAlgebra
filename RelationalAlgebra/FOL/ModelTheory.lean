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

variable {t t' : String →. μ} {rs rs' : Finset String} [DecidableEq String] [Nonempty μ]

@[simp]
instance fintype_dom (h : t.Dom = rs) : Fintype ↑t.Dom := by
  apply Fintype.ofFinset rs (Set.ext_iff.mp h.symm)

@[simp]
instance decidable_dom (h : t.Dom = rs) : ∀a, Decidable (t a).Dom := by
  intro a
  simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
  exact Finset.decidableMem a rs

@[simp]
noncomputable def TupleToFun (h : t.Dom = rs) : String → μ :=
  by
    haveI := decidable_dom h
    exact λ a => (t a).getOrElse (Classical.arbitrary μ)

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

variable {μ : Type} {rs: Finset String} [Nonempty μ]

def ArityToTuple (va : Fin rs.card → μ) : String →. μ :=
  λ att => dite (att ∈ rs) (λ h => va (RelationSchema.index h)) (λ _ => Part.none)

@[simp]
theorem ArityToTuple.def_dite (va : Fin rs.card → Value) :
  ArityToTuple va = λ att => dite (att ∈ rs) (λ h => .some (va (RelationSchema.index h))) (λ _ => Part.none) := by
    rfl

theorem ArityToTuple.def_fromIndex {t : String →. μ} (h : t.Dom = ↑rs) :
  ArityToTuple (fun i : Fin rs.card ↦ (TupleToFun h (RelationSchema.fromIndex i))) = t := by
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
inductive relations (dbs : String → Finset String) : ℕ → Type
  | R : (rn : String) → relations dbs (dbs rn).card

/-- The language of fol contains the relations -/
def Language.fol (dbs : String → Finset String) : Language :=
  { Functions := fun _ => Empty
    Relations := relations dbs }
  deriving Language.IsRelational

@[simp]
def fol.Rel {dbs: String → Finset String} (rn: String) : (Language.fol dbs).Relations (dbs rn).card :=
  relations.R rn


open Language

class folStruc (dbi : DatabaseInstance String String μ) extends (fol dbi.schema).Structure μ where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      (rn : String)          →                      -- Every relation (and every arity)
      (va : Fin (dbi.schema rn).card → μ) →             -- Every value assignment (for this arity)

        RelMap (.R rn) va ↔                             -- Then the RelationMap contains the relation for this value assignment
        (                                                   -- @TODO, Update the comments  - Iff this value assignment corresponds with a tuple in the relation instance
          ArityToTuple va ∈ (dbi.relations rn).tuples
        )

@[simp]
theorem folStruc_apply_RelMap (dbi : DatabaseInstance String String μ) [folStruc dbi] {rn} {va : Fin (dbi.schema rn).card → μ} :
  Structure.RelMap (fol.Rel rn) va ↔ ArityToTuple va ∈ (dbi.relations rn).tuples
    := (folStruc.RelMap_R rn va)

@[simp]
theorem fol_empty_fun (_f : (fol dbs).Functions n) : False := by
  exact Aesop.BuiltinRules.empty_false _f

theorem Term.cases (t : (fol dbs).Term (α ⊕ (Fin n))) : ∃k, t = var k := by
  cases t with | var k => use k | func _f _ => exact False.elim (fol_empty_fun _f)

end folStruc
