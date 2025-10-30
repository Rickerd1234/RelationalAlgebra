import Mathlib.Data.Set.Basic
import Mathlib.Data.PFun
import Mathlib.Data.Finset.Defs

namespace RM

-- Define the Relational Model
section RelationalModel

variable {α ρ μ : Type}


structure RelationInstance (α μ : Type) where
    schema : Finset α
    tuples : Set (α →. μ)
    validSchema : ∀ t : (α →. μ), t ∈ tuples → t.Dom = schema

structure DatabaseInstance (ρ α μ : Type) where
    schema : ρ → Finset α
    relations : ρ → RelationInstance α μ
    validSchema : ∀ rel : ρ, (relations rel).schema = schema rel

end RelationalModel


-- Basic proofs
@[simp]
theorem RelationInstance.validSchema.ext {inst : RelationInstance α μ} (h : t ∈ inst.tuples) :
  (t a).Dom ↔ a ∈ inst.schema := Set.ext_iff.mp (inst.validSchema t h) a

@[simp]
theorem DatabaseInstance.validSchema.ext {dbi : DatabaseInstance ρ α μ} (rn : ρ) :
  a ∈ (dbi.relations rn).schema ↔ a ∈ dbi.schema rn := Finset.ext_iff.mp (dbi.validSchema rn) a
