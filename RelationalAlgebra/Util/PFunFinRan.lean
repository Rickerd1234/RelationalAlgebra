import Mathlib.Data.PFun
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.PImage

variable {α β : Type} (f : PFun α β)

@[simp]
theorem ran_mem {b : β} : (∃a, f a = Part.some b) ↔ b ∈ f.ran
    := by simp_all only [Part.eq_some_iff, PFun.ran, Set.mem_setOf_eq]

variable [DecidableEq α] [DecidableEq β] [Fintype f.Dom]

@[simp]
instance (a : α) : Decidable (f a).Dom := by
  simp only [Part.dom_iff_mem, ← PFun.mem_dom, Finset.mem_coe]
  exact f.Dom.decidableMemOfFintype a

@[simp]
theorem ran_def_finset : f.ran = f.Dom.toFinset.pimage f := by
  ext x
  simp_all only [PFun.ran, PFun.Dom]
  simp [Part.dom_iff_mem, PFun.image_def]
  aesop

@[simp]
instance : Fintype f.ran := by
  rw [ran_def_finset]
  exact FinsetCoe.fintype (Finset.pimage f f.Dom.toFinset)
