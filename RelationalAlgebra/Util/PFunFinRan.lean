import Mathlib.Data.PFun
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.PImage

variable {α β : Type} (f : PFun α β)

theorem ran_mem {b : β} : b ∈ f.ran ↔ (∃a, f a = Part.some b)
    := by simp_all only [Part.eq_some_iff, PFun.ran, Set.mem_setOf_eq]

variable [DecidableEq α] [DecidableEq β] [Fintype f.Dom]

instance (a : α) : Decidable (f a).Dom := by
  simp only [Part.dom_iff_mem, ← PFun.mem_dom]
  exact f.Dom.decidableMemOfFintype a

theorem ran_def_finset : f.Dom.toFinset.pimage f = f.ran := by
  ext x
  simp_all only [PFun.ran, PFun.Dom]
  simp [Part.dom_iff_mem, PFun.image_def]
  aesop

instance : Fintype f.ran := by
  rw [← ran_def_finset]
  exact FinsetCoe.fintype (Finset.pimage f f.Dom.toFinset)
