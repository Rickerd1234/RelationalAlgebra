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

-- All values in the database
def DatabaseInstance.domain (dbi : DatabaseInstance ρ α μ) : Set μ :=
    {v | ∃rn att, Part.some v ∈ (dbi.relations rn).tuples.image (λ tup => tup att)}

theorem DatabaseInstance.domain.t_ran_def {dbi : DatabaseInstance ρ α μ} (ht : t ∈ (dbi.relations rn).tuples) :
  t.ran ⊆ dbi.domain := by
    simp_rw [Set.subset_def, PFun.ran, DatabaseInstance.domain, Set.mem_setOf_eq, Set.mem_image, forall_exists_index]
    intro v a hv
    use rn, a, t
    apply And.intro ht (Part.eq_some_iff.mpr hv)
