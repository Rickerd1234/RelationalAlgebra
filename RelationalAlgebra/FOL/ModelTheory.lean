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


/-
Partial function (Tuple) to complete function.
Required to ensure that the structure has `μ` type, instead of `Part μ`
-/
section TupleToFun

variable {t t' : α →. μ} {rs rs' : Finset α} [DecidableEq α] [Nonempty μ]

@[simp]
instance fintype_dom (h : t.Dom = rs) : Fintype ↑t.Dom := by
  apply Fintype.ofFinset rs (Set.ext_iff.mp h.symm)

@[simp]
instance decidable_dom (h : t.Dom = rs) : ∀a, Decidable (t a).Dom := by
  intro a
  simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
  exact Finset.decidableMem a rs

/-- Convert a partial function `t`, with `t.Dom = rs` into a total function -/
@[simp]
noncomputable def TupleToFun (h : t.Dom = rs) : α → μ :=
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
theorem TupleToFun.tuple_eq_self (h : t.Dom = rs) (h' : t.Dom = rs') :
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

@[simp]
theorem TupleToFun.tuple_eq_iff (h : t.Dom = rs) (ha : (t a).Dom) (hb : (t b).Dom) :
  TupleToFun h a = TupleToFun h b ↔ t a = t b := by
    simp_all [Part.getOrElse_of_dom, Part.eq_iff_of_dom]

end TupleToFun


/-
Define variable indexing types.
This is required for the conversion from unnamed `ModelTheory` to named `RelationInstance`
-/
section ArityToTuple

variable {μ : Type} {rs: Finset α} [DecidableEq α]
  [LE α] [DecidableRel (α := α) fun x1 x2 ↦ x1 ≤ x2] [IsTrans α fun x1 x2 ↦ x1 ≤ x2]
  [IsAntisymm α fun x1 x2 ↦ x1 ≤ x2] [IsTotal α fun x1 x2 ↦ x1 ≤ x2]

/-- Convert a arity mapping `va` for a relation into a tuple function `t` -/
def ArityToTuple (va : Fin rs.card → μ) : α →. μ :=
  λ att => dite (att ∈ rs) (λ h => va (RelationSchema.index h)) (λ _ => Part.none)

@[simp]
theorem ArityToTuple.def_dite (va : Fin rs.card → μ) :
  ArityToTuple va = λ att => dite (att ∈ rs) (λ h => .some (va (RelationSchema.index h))) (λ _ => Part.none) := by
    rfl

theorem ArityToTuple.def_fromIndex [Nonempty μ] {t : α →. μ} (h : t.Dom = ↑rs) :
  ArityToTuple (fun i : Fin rs.card ↦ (TupleToFun h (RelationSchema.fromIndex i))) = t := by
    simp
    ext a v
    have : (t a).Dom ↔ a ∈ rs := by exact Iff.symm (Eq.to_iff (congrFun (id (Eq.symm h)) a))
    split
    all_goals simp_all [Part.getOrElse, Part.dom_iff_mem]

end ArityToTuple


-- Define relation concept for FOL
section language

open FirstOrder

variable {ρ μ α : Type}

/-- The type of Relations in FOL -/
inductive relations (dbs : ρ → Finset α) : ℕ → Type
  | R : (rn : ρ) → relations dbs (dbs rn).card

/-- The language of fol contains the relations -/
def Language.fol (dbs : ρ → Finset α) : Language :=
  { Functions := fun _ => Empty
    Relations := relations dbs }
  deriving Language.IsRelational

@[simp]
def fol.Rel {dbs: ρ → Finset α} (rn: ρ) : (Language.fol dbs).Relations (dbs rn).card :=
  relations.R rn


open Language

section struc

variable [DecidableEq α]
  [LE α] [DecidableRel (α := α) fun x1 x2 ↦ x1 ≤ x2] [IsTrans α fun x1 x2 ↦ x1 ≤ x2]
  [IsAntisymm α fun x1 x2 ↦ x1 ≤ x2] [IsTotal α fun x1 x2 ↦ x1 ≤ x2]

/--
The definition of the structure in ModelTheory, dependent on a `DatabaseInstance`.
A relation `rn` and arity assignment `va` are satisfiable if and only if `ArityToTuple va ∈ (dbi.relations rn).tuples`.
Meaning that the relation contains the tuple corresponding with the unnamed to named perspective conversion of `va`.
 -/
class folStruc (dbi : DatabaseInstance ρ α μ) extends (fol dbi.schema).Structure μ where
  RelMap_R :
      (rn : ρ) →
      (va : Fin (dbi.schema rn).card → μ) →

        RelMap (.R rn) va ↔
        (
          ArityToTuple va ∈ (dbi.relations rn).tuples
        )

@[simp]
theorem folStruc_apply_RelMap (dbi : DatabaseInstance ρ String μ) [folStruc dbi] {rn} {va : Fin (dbi.schema rn).card → μ} :
  Structure.RelMap (fol.Rel rn) va ↔ ArityToTuple va ∈ (dbi.relations rn).tuples
    := (folStruc.RelMap_R rn va)

@[simp]
theorem fol_empty_fun (_f : (fol dbs).Functions n) : False := by
  exact Aesop.BuiltinRules.empty_false _f

end struc

theorem Term.cases (t : (fol dbs).Term (α ⊕ (Fin n))) : ∃k, t = var k := by
  cases t with | var k => use k | func _f _ => exact False.elim (fol_empty_fun _f)

end language
