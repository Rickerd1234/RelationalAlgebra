import Mathlib.Data.Set.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Finset.Defs

namespace RM

-- Define the Relational Model
section RelationalModel

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

end RelationalModel


-- Basic proofs
@[simp]
theorem RelationInstance.validSchema.ext {a t} {inst : RelationInstance} (h : t ∈ inst.tuples) :
  (t a).Dom ↔ a ∈ inst.schema := Set.ext_iff.mp (inst.validSchema t h) a

@[simp]
theorem DatabaseInstance.validSchema.ext {dbi : DatabaseInstance} (rn : RelationName) :
  a ∈ (dbi.relations rn).schema ↔ a ∈ dbi.schema rn := Finset.ext_iff.mp (dbi.validSchema rn) a
