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

noncomputable def FreeMap (n : ℕ) (brs : Finset String) : Fin n → String :=
  match n with
  | .zero => Fin.elim0
  | .succ i => liftF (FreeMap i brs) brs

theorem FRan.FreeMap_lift_union : FRan (FreeMap n brs) ∪ FRan (FreeMap (n + 1) brs) = FRan (FreeMap (n + 1) brs) := by
  rw [FreeMap, liftF_union]

theorem FRan.lift_insert : FRan (Fin.snoc f v) = insert (v) (FRan f) := by
  simp [FRan, FRanS]
  ext a
  simp_all only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_insert]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    subst h
    induction w using Fin.lastCases with
    | cast j => simp
    | last => simp
  · intro a_1
    cases a_1 with
    | inl h =>
      subst h
      use Fin.last _
      simp
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      subst h
      use w.castSucc
      simp

theorem FreeMap.mem_def : FreeMap n brs i ∈ brs ∨ FreeMap n brs i = Classical.arbitrary String := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n' ih =>
    simp [FreeMap, liftF]
    induction i using Fin.lastCases with
    | cast j => simp; apply ih
    | last =>
      simp_all only [Fin.snoc_last]
      rw [@List.getD_getElem?]
      split
      next h =>
        apply Or.inl
        rw [← RelationSchema.ordering_mem]
        grind
      next h => simp

theorem FreeMap.fromIndex_brs_def {i : Fin n} (h : n ≤ brs.card) : FreeMap n brs i = RelationSchema.fromIndex (i.castLE h) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n' ih =>
    simp [FreeMap, liftF]
    induction i using Fin.lastCases with
    | cast j => simp; apply ih;
    | last =>
      simp only [Fin.snoc_last, RelationSchema.fromIndex, Fin.cast_castLE, List.get_eq_getElem,
        Fin.coe_castLE, Fin.val_last]
      rw [@List.getD_getElem?]
      simp only [RelationSchema.ordering_card]
      grind only

theorem FRan.mem_FreeMap_lift_cases (h : n + 1 ≤ brs.card) : x ∈ FRan (FreeMap (n + 1) brs) ↔ (x ∈ FRan (FreeMap n brs) ∨ x = FreeMap (n + 1) brs (Fin.last n)) := by
  apply Iff.intro
  · intro a
    simp [FRan, FreeMap, FRanS, liftF] at a
    obtain ⟨i, hi⟩ := a
    induction i using Fin.lastCases with
    | cast j => apply Or.inl; subst hi; simp
    | last =>
      simp at hi
      apply Or.inr
      subst hi
      rw [FreeMap.fromIndex_brs_def h]
      . rw [RelationSchema.fromIndex]
        simp
        rw [@List.getD_getElem?]
        have : n < (RelationSchema.ordering brs).length := by simp; grind
        simp only [this, ↓reduceDIte]
  · intro a
    cases a with
    | inl h => exact FRan.liftF_sub h
    | inr h_1 =>
      subst h_1
      simp_all only [mem_def]

theorem FreeMap.inj_n (h : n ≤ brs.card) : (FreeMap n brs).Injective := by
  simp [Function.Injective]
  intro a₁ a₂ h'
  rw [FreeMap.fromIndex_brs_def h, FreeMap.fromIndex_brs_def h] at h'
  have := RelationSchema.fromIndex_inj.mp h'
  simp_all

theorem FreeMap.FRan_card_def (h : n ≤ brs.card) : (FRan (FreeMap n brs)).card = n :=
  FRan.card_def (inj_n h)

theorem FreeMap.get_def : (FreeMap (n + 1) brs) (Fin.last n) = (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) brs)[n]'h := by
  simp [FreeMap, liftF, RelationSchema.ordering]
  rw [@List.getD_getElem?]
  split
  . simp
  . simp

-- instance antiSymm : IsAntisymm String fun x1 x2 ↦ x1 ≥ x2 := by exact IsAntisymm.swap LE.le
-- instance total : IsTotal String fun x1 x2 ↦ x1 ≥ x2 := by exact IsTotal.swap LE.le

-- theorem reverse_sort_insert {rs : Finset String} : (Finset.sort (.≤.) rs) = List.reverse (Finset.sort (.≥.) rs) := by
--   sorry

-- theorem FreeMap.FRan_ordering_def (h : n ≤ brs.card) : RelationSchema.ordering (FRan (FreeMap n brs)) = (RelationSchema.ordering brs).take n := by
--   simp [RelationSchema.ordering]
--   induction n with
--   | zero => simp [FRan, FRanS]
--   | succ n ih =>
--     simp [FreeMap, liftF, FRan.lift_insert]

--     rw [List.take_add_one]
--     have : (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) brs)[n]?.isSome := by simp; grind
--     simp at this
--     simp only [RelationSchema.ordering_card, this, getElem?_pos, Option.getD_some,
--       Finset.length_sort, Option.toList_some]
--     simp_rw [reverse_sort_insert]
--     rw [Finset.sort_insert]
--     . simp_rw [List.reverse_cons, List.getElem_reverse, ← reverse_sort_insert]
--       simp_rw [ih (by grind)]
--       sorry
--     . sorry
--     . sorry




-- theorem FreeMap.fromIndex_FRan_def {i : Fin n} (h : n ≤ (FRan (FreeMap n brs)).card) (h' : n ≤ brs.card) : FreeMap n brs i = RelationSchema.fromIndex (i.castLE h) := by
--   induction n with
--   | zero => exact Fin.elim0 i
--   | succ n' ih =>
--     simp [FreeMap, liftF]
--     induction i using Fin.lastCases with
--     | cast j =>
--       simp only [Fin.snoc_castSucc, Fin.castLE_castSucc]
--       have := ih (i := j) (by rw [FreeMap.FRan_card_def (Nat.le_of_succ_le h')]) (Nat.le_of_succ_le h')
--       simp [this, RelationSchema.fromIndex]
--     | last =>
--       simp only [Fin.snoc_last, RelationSchema.fromIndex, Fin.cast_castLE, List.get_eq_getElem,
--         Fin.coe_castLE, Fin.val_last]
--       rw [@List.getD_getElem?]
--       simp only [RelationSchema.ordering_card]
--       grind only

-- theorem FreeMap.self_def (h : a ∈ FRan (FreeMap n brs)) (h' : n ≤ brs.card) :
--   FreeMap n brs ((RelationSchema.index h).castLE (by rw [FRan.card_def (inj_n h')])) = a := by
--     have ⟨i, hi⟩ : ∃i : Fin (FRan (FreeMap n brs)).card, RelationSchema.fromIndex i = a := by
--       use RelationSchema.index h; simp
--     subst hi
--     rw [RelationSchema.index_fromIndex_eq, fromIndex_FRan_def _ h']
--     simp_rw [Fin.castLE]
--     rw [FRan.card_def (inj_n h')]

theorem FRan.notMem_FreeMap_lift (h : n + 1 ≤ brs.card) : FreeMap (n + 1) brs (Fin.last n) ∉ FRan (FreeMap n brs) := by
  rw [FRan]
  unfold FRanS
  simp only [FreeMap, liftF, List.getD_eq_getElem?_getD, Fin.snoc_last, Set.mem_toFinset,
    Set.mem_setOf_eq, not_exists, List.getD_getElem?, RelationSchema.ordering_card]
  intro i
  have : n < brs.card := by grind
  simp only [this, ↓reduceDIte, ne_eq]
  rw [@RelationSchema.fromIndex_eq_get, FreeMap.fromIndex_brs_def (by grind), Fin.castLE]
  by_contra hc
  rw [RelationSchema.fromIndex_inj] at hc
  grind
