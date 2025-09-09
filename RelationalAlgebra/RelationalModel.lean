import Mathlib.Data.Set.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Finset.Defs

namespace RM

abbrev Attribute := String

abbrev RelationName := String

abbrev Value := Nat

abbrev RelationSchema := Finset Attribute

abbrev Tuple := Attribute →. Value

structure RelationInstance where
    schema : RelationSchema
    tuples : Set Tuple
    validSchema : ∀ t : Tuple, t ∈ tuples → t.Dom = schema

abbrev DatabaseSchema := RelationName → RelationSchema

structure DatabaseInstance where
    schema : DatabaseSchema
    relations : RelationName → RelationInstance
    validSchema : ∀ rel : RelationName, (relations rel).schema = schema rel


-- Database instance variable domain
def DatabaseInstance.domain (dbi : DatabaseInstance) : Set Value :=
    {v | ∃rn att, Part.some v ∈ (dbi.relations rn).tuples.image (λ tup => tup att)}


-- Basic proofs
@[simp]
theorem RelationInstance.validSchema.def {t} {inst : RelationInstance} (h : t ∈ inst.tuples) :
  t.Dom = inst.schema := by simp_all [inst.validSchema]

@[simp]
theorem RelationInstance.validSchema.iff_def {a t} {inst : RelationInstance} (h : t ∈ inst.tuples) :
  a ∈ inst.schema ↔ (t a).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, RelationInstance.validSchema.def h, Finset.mem_coe]

@[simp]
theorem DatabaseInstance.validSchema_def {dbi : DatabaseInstance} (rn : RelationName) :
  (dbi.relations rn).schema = dbi.schema rn := by simp_all [dbi.validSchema]

@[simp]
theorem DatabaseInstance.t_ran_sub_domain {dbi : DatabaseInstance} {rn : RelationName} (h : t ∈ (dbi.relations rn).tuples) :
  t.ran ⊆ dbi.domain := by
    simp_all [domain, PFun.ran]
    intros v a h'
    use rn, a, t, h
    exact Part.eq_some_iff.mpr h'

@[simp]
theorem DatabaseInstance.default_ran_sub_domain {dbi : DatabaseInstance} :
  (default : Fin 0 →. Value).ran ⊆ dbi.domain := by
    simp [default, PFun.ran]
