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
def FRan.card_def {f : Fin n → String} (hf : f.Injective) : (FRan f).card = n := by
  induction n
  . simp [FRan, FRanS]
  . rename_i n' ih
    rw [@Finset.card_eq_succ_iff_cons]
    use f 0
    use FRan (Fin.tail f)
    simp_all only [Finset.cons_eq_insert, exists_and_left, exists_prop]
    apply And.intro
    · ext a
      simp [FRan, FRanS]
      apply Iff.intro
      · intro a_1
        cases a_1 with
        | inl h =>
          subst h
          simp_all only [exists_apply_eq_apply]
        | inr h_1 =>
          obtain ⟨w, h⟩ := h_1
          subst h
          use w.succ
          rfl
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        subst h
        by_cases hc : ↑w = 0
        . simp_all
        . apply Or.inr
          use w.pred hc
          simp [Fin.tail]
    · apply And.intro
      · simp [FRan, FRanS, Fin.tail]
        simp [Function.Injective] at hf
        intro x
        by_contra hc
        exact (Fin.succ_ne_zero x) (hf hc)
      · simp [FRan]
        rw [Finset.card_image_of_injective]
        . simp
        . rw [Fin.tail_def, ← Function.comp_def]
          exact Function.Injective.comp hf (Fin.succ_injective n')

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
