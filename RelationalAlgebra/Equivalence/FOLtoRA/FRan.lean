import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.Ordering
import Mathlib.Data.Finset.Fin

open RM

def FRanS (f : Fin n → String) : Set String := {a | ∃i, f i = a}

instance FRanSFin {f : Fin n → String} : Fintype (FRanS f) := by
  apply Fintype.ofFinset (((Finset.range n).attachFin (by intro n h; simp at h; apply h)).image f)
  . simp [FRanS]

def FRan (f : Fin n → String) : Finset String := (FRanS f).toFinset

@[simp]
def FRan.default := FRan Fin.elim0

@[simp]
theorem FRan.default_eq_empty : FRan Fin.elim0 = ∅ := by simp [FRan, FRanS]

@[simp]
theorem FRan.mem_def : f i ∈ FRan f := by simp [FRan, FRanS]

noncomputable def liftF (f' : Fin n → String) (brs : Finset String) : Fin (n + 1) → String :=
  Fin.snoc f' ((RelationSchema.ordering brs).getD n (Classical.arbitrary String))

@[simp]
theorem FRan.liftF_sub {f : Fin n → String} : FRan f ⊆ FRan (liftF f brs) := by
  simp [FRan, FRanS, liftF]
  intro i
  use i.castLE (Nat.le_add_right n 1)
  simp_all [Fin.snoc]
  rfl

@[simp]
theorem FRan.liftF_union {f : Fin n → String} : FRan f ∪ FRan (liftF f brs) = FRan (liftF f brs) := Finset.union_eq_right.mpr liftF_sub

@[simp]
theorem FRan.liftF_sub_brs {f : Fin n → String} (h : n < brs.card) (h' : FRan f ⊆ brs) : FRan (liftF f brs) ⊆ brs := by
  simp [FRan, FRanS, liftF] at h' ⊢
  intro i h
  obtain ⟨w, h⟩ := h
  subst h
  by_cases hc : w = Fin.last n
  . subst hc
    simp
    rw [← RelationSchema.ordering_mem, @List.getD_getElem?]
    simp [h]
  . have : ↑w < n := Fin.lt_last_iff_ne_last.mpr hc
    simp [Fin.snoc, this]
    simp [Set.subset_def] at h'
    simp [h']

@[simp]
theorem FRan.liftF_union_brs {f : Fin n → String} (h : n < brs.card) (h' : FRan f ⊆ brs) : (brs ∪ FRan (liftF f brs)) = brs := Finset.union_eq_left.mpr (liftF_sub_brs h h')
