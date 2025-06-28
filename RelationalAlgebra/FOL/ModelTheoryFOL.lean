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

abbrev MTVar (dbi: DatabaseInstance) (rn : RelationName) := Fin (dbi.schema rn).card
abbrev MTVarAssignment (dbi: DatabaseInstance) (rn : RelationName) := MTVar dbi rn → Part Value

def assignmentToTuple {dbi: DatabaseInstance} {rn : RelationName} (va : MTVarAssignment dbi rn) : Tuple :=
  λ att => (((dbi.schema rn).index? att).map va).getD Part.none

theorem assignmentToTuple_def {t : Tuple} {dbi: DatabaseInstance} {rn : RelationName} {va : MTVarAssignment dbi rn}
  : t ∈ (dbi.relations rn).tuples → (assignmentToTuple va = t ↔ ∀i, va i = t ((dbi.schema rn).fromIndex i))
    := by
      intro h
      apply Iff.intro
      · intro a i
        subst a
        simp_all [assignmentToTuple, RelationSchema.index?, Option.map, RelationSchema.ordering, Option.getD, RelationSchema.fromIndex, MTVar]
        split
        next opt x heq =>
          split at heq
          next opt_1 x_1 heq_1 =>
            split at heq_1
            next opt_2 x_2
              heq_2 =>
              simp_all only [Option.some.injEq, List.finIdxOf?_eq_some_iff, Fin.getElem_fin]
              subst heq_1 heq
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
      . intro h
        ext a b
        simp_all [assignmentToTuple, RelationSchema.index?, Option.map, RelationSchema.ordering, Option.getD, RelationSchema.fromIndex, MTVar]
        apply Iff.intro
        · intro a_2
          split at a_2
          next opt x heq =>
            split at heq
            next opt_1 x_1 heq_1 =>
              split at heq_1
              next opt_2 x_2
                heq_2 =>
                simp_all only [Option.some.injEq, List.finIdxOf?_eq_some_iff, Fin.getElem_fin]
                subst heq heq_1
                simp_all only
              next opt_2 heq_2 =>
                simp_all only [Option.some.injEq, List.finIdxOf?_eq_none_iff, Finset.mem_sort, reduceCtorEq]
            next opt_1 heq_1 =>
              split at heq_1
              next opt_2 x_1 heq_2 => simp_all only [reduceCtorEq]
              next opt_2 heq_2 => simp_all only [reduceCtorEq]
          next opt heq =>
            split at heq
            next opt_1 x heq_1 =>
              split at heq_1
              next opt_2 x_1 heq_2 => simp_all only [Part.not_mem_none]
              next opt_2 heq_2 => simp_all only [Part.not_mem_none]
            next opt_1 heq_1 =>
              split at heq_1
              next opt_2 x heq_2 => simp_all only [Part.not_mem_none]
              next opt_2 heq_2 => simp_all only [Part.not_mem_none]
        · intro a_2
          split
          next opt x heq =>
            split at heq
            next opt_1 x_1 heq_1 =>
              split at heq_1
              next opt_2 x_2
                heq_2 =>
                simp_all only [Option.some.injEq, List.finIdxOf?_eq_some_iff, Fin.getElem_fin]
                subst heq heq_1
                simp_all only
              next opt_2 heq_2 =>
                simp_all only [Option.some.injEq, List.finIdxOf?_eq_none_iff, Finset.mem_sort, reduceCtorEq]
            next opt_1 heq_1 =>
              split at heq_1
              next opt_2 x_1 heq_2 => simp_all only [reduceCtorEq]
              next opt_2 heq_2 => simp_all only [reduceCtorEq]
          next opt heq =>
            simp_all only [Part.not_mem_none]
            split at heq
            next opt_1 x heq_1 =>
              split at heq_1
              next opt_2 x_1 heq_2 => simp_all only [reduceCtorEq]
              next opt_2 heq_2 => simp_all only [reduceCtorEq]
            next opt_1 heq_1 =>
              split at heq_1
              next opt_2 x heq_2 => simp_all only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, reduceCtorEq]
              next opt_2 heq_2 =>
                simp_all only [List.finIdxOf?_eq_none_iff, Finset.mem_sort]
                -- Patch required for aesop
                have z : ∀x, x ∈ dbi.schema rn ↔ x ∈ t.Dom := by
                  simp_all only [dbi.validSchema, (dbi.relations rn).validSchema, Finset.mem_coe, implies_true]
                apply heq_2
                simp_all only [PFun.mem_dom, not_exists, exists_const]



-- Explore relation concepts
class folStruc extends fol.Structure (Part Value) where
  RelMap_R :      -- Add proof to RelMap for each Relation in the Language
      (dbi : DatabaseInstance)     →                      -- Every database instance
      (rn : RelationName)          →                      -- Every relation (and every arity)
      (va : MTVarAssignment dbi rn) →                     -- Every value assignment (for this arity)
        assignmentToTuple va ∈ (dbi.relations rn).tuples  -- Iff this value assignment corresponds with a tuple in the relation instance
          ↔ RelMap (.R dbi rn) va                         -- Then the RelationMap contains the relation for this value assignment


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
theorem brtr_schema_dbi_def {n : ℕ} (brtr : BoundedRelationTermRestriction n) : brtr.dbi.schema brtr.name = brtr.schema := by
  simp only [RelationTermRestriction.schema, brtr.validSchema, Finset.toFinset_coe]

theorem brtr_dom {n : ℕ} {brtr : BoundedRelationTermRestriction n} (i : MTVar brtr.dbi brtr.name) :
  (brtr.inFn ((brtr.dbi.schema brtr.name).fromIndex i)).Dom
    := by
    apply Part.dom_iff_mem.mpr
    apply (PFun.mem_dom brtr.inFn (RelationSchema.fromIndex i)).mp
    rw [brtr.validSchema]
    simp only [← brtr_schema_dbi_def, Finset.mem_coe, RelationSchema.fromIndex_mem]

def getMap {n : ℕ} (brtr : BoundedRelationTermRestriction n) : MTVar brtr.dbi brtr.name → VariableTerm n :=
  λ i => (brtr.inFn (RelationSchema.fromIndex i)).get (brtr_dom i)
