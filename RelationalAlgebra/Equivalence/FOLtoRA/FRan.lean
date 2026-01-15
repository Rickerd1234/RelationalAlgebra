import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.Ordering
import Mathlib.Data.Finset.Fin

open RM

section FRan

variable {α : Type} [DecidableEq α]

/-- `Finset` equal to the range of `f`. -/
def FRan (f : Fin n → α) : Finset α := (Set.range f).toFinset

@[simp]
def FRan.card_def {f : Fin n → α} (hf : f.Injective) : (FRan f).card = n := by
  induction n
  . simp [FRan]
  . rename_i n' ih
    rw [@Finset.card_eq_succ_iff_cons]
    use f 0
    use FRan (Fin.tail f)
    simp_all only [Finset.cons_eq_insert, exists_and_left, exists_prop]
    apply And.intro
    · ext a
      simp [FRan]
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
      · simp [FRan, Fin.tail]
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
def FRan.default := FRan Fin.elim0 (α := α)

@[simp]
theorem FRan.default_eq_empty : FRan Fin.elim0 (α := α) = ∅ := by simp [FRan]

@[simp]
theorem FRan.mem_def {f : Fin n → α}: f i ∈ FRan f := by simp [FRan]

end FRan

section FreeMap

variable [LinearOrder α] [Inhabited α] {brs : Finset α}

/--
Mapping for bound variables `Fin n` to a deterministic `α` used as variable in the RA query.
Requires `brs.card > n` to prevent falling back to `α.default`.
-/
def FreeMap (n : ℕ) (brs : Finset α) : Fin n → α :=
  λ i => (RelationSchema.ordering brs).getD i (default)


/- A bunch of helper theorems to reason about the `FreeMap` and `FRan` defintions. -/
theorem FreeMap.FRan_def (h : n ≤ brs.card) : FRan (FreeMap n brs) = ((RelationSchema.ordering brs).take n).toFinset := by
  simp [Set.range, FRan, FreeMap]
  ext a
  simp only [List.getD_eq_getElem?_getD, Set.mem_toFinset, Set.mem_setOf_eq, List.mem_toFinset]
  apply Iff.intro
  . intro ⟨w, h_1⟩
    subst h_1
    rw [@List.getD_getElem?]
    induction n with
    | zero => apply Fin.elim0 w
    | succ n' ih =>
      induction w using Fin.lastCases with
      | cast j =>
        simp only [List.take_add_one, Fin.coe_castSucc, List.mem_append, Option.mem_toList]
        apply Or.inl
        exact ih (by grind) j
      | last =>
        simp [List.take_add_one]
        apply Or.inr
        have : n' < brs.card := by grind
        simp [this]
  . intro h_1
    rw [List.mem_take_iff_getElem] at h_1
    simp_all only [RelationSchema.ordering_card, inf_of_le_left]
    obtain ⟨w, h_1⟩ := h_1
    obtain ⟨w_1, h_1⟩ := h_1
    subst h_1
    use ⟨w, w_1⟩
    rw [@List.getD_getElem?]
    have : w < brs.card := by grind
    simp [this]

theorem List.take_sorted [LinearOrder α'] (l : List α') : List.Sorted (.≤.) l → List.Sorted (.≤.) (List.take n l) := by
  intro h
  induction l generalizing n
  . simp
  . simp_all only [List.sorted_cons, forall_const]
    obtain ⟨left, right⟩ := h
    by_cases hc : n = 0
    . subst hc
      simp
    . rw [List.take_cons (Nat.zero_lt_of_ne_zero hc)]
      simp_all only [List.sorted_cons]
      apply And.intro
      · intro b a
        have := List.mem_of_mem_take a
        simp_all
      · simp

theorem List.take_nodup (l : List α') : List.Nodup l → List.Nodup (List.take n l) := by
  intro h
  induction l generalizing n
  . simp
  . simp_all only [List.nodup_cons, forall_const]
    obtain ⟨left, right⟩ := h
    by_cases hc : n = 0
    . subst hc
      simp
    . rw [List.take_cons (Nat.zero_lt_of_ne_zero hc)]
      simp_all only [List.nodup_cons]
      apply And.intro
      · intro a
        have := List.mem_of_mem_take a
        simp_all
      · simp

theorem FreeMap.FRan_ordering_def (h : n ≤ brs.card) : RelationSchema.ordering (FRan (FreeMap n brs)) = (RelationSchema.ordering brs).take n := by
  rw [FreeMap.FRan_def h]
  rw [RelationSchema.ordering]
  refine (List.toFinset_sort (fun x1 x2 ↦ x1 ≤ x2) ?_).mpr ?_
  . exact List.take_nodup (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) brs) (Finset.sort_nodup (fun x1 x2 ↦ x1 ≤ x2) brs)
  . exact List.take_sorted (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) brs) (Finset.sort_sorted (fun x1 x2 ↦ x1 ≤ x2) brs)

theorem FreeMap.add_one_def {brs : Finset α} : FreeMap (n + 1) brs j.castSucc = FreeMap n brs j := by
  rfl

@[simp]
theorem FreeMap.FRan_sub_add_one (h : n + 1 ≤ brs.card) : FRan (FreeMap n brs) ⊆ FRan (FreeMap (n + 1) brs) := by
  rw [FreeMap.FRan_def h, FreeMap.FRan_def (Nat.le_of_succ_le h)]
  rw [Finset.subset_iff]
  intro a ha
  simp [List.take_add_one, ha]


@[simp]
theorem FreeMap.FRan_sub_brs (h : n ≤ brs.card) : FRan (FreeMap n brs) ⊆ brs := by
  rw [FreeMap.FRan_def h]
  rw [Finset.subset_iff]
  intro a ha
  rw [List.mem_toFinset] at ha
  rw [← RelationSchema.ordering_mem]
  exact List.mem_of_mem_take ha

@[simp]
theorem FreeMap.notMem_notMem_FRan (h : n ≤ brs.card) : x ∉ brs → x ∉ FRan (FreeMap n brs) := by
  intro a
  apply Aesop.BuiltinRules.not_intro
  intro a_1
  apply a
  apply FreeMap.FRan_sub_brs h a_1

@[simp]
theorem FreeMap.FRan_union_add_one (h : n + 1 ≤ brs.card) : FRan (FreeMap n brs) ∪ FRan (FreeMap (n + 1) brs) = FRan (FreeMap (n + 1) brs) := by
  simp [h]

theorem FreeMap.mem_def' {brs : Finset α} : FreeMap n brs i ∈ brs ∨ FreeMap n brs i = default := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n' ih =>
    simp [FreeMap]
    induction i using Fin.lastCases with
    | cast j => simp; apply ih
    | last =>
      rw [@List.getD_getElem?]
      split
      next h =>
        apply Or.inl
        rw [← RelationSchema.ordering_mem]
        grind
      next h => simp

theorem FreeMap.mem_def {brs : Finset α} {i : Fin n} (h : ↑i < brs.card) : FreeMap n brs i ∈ brs := by
  rw [← RelationSchema.ordering_mem]
  rw [FreeMap]
  rw [@List.mem_iff_getElem]
  use ↑i
  simp_all

theorem FreeMap.fromIndex_brs_def {brs : Finset α} {i : Fin n} (h : n ≤ brs.card) :
  FreeMap n brs i = RelationSchema.fromIndex (i.castLE h) := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n' ih =>
      simp [FreeMap]
      induction i using Fin.lastCases with
      | cast j => simp; apply ih;
      | last =>
        simp only [RelationSchema.fromIndex, Fin.cast_castLE, List.get_eq_getElem, Fin.coe_castLE, Fin.val_last]
        rw [@List.getD_getElem?]
        simp only [RelationSchema.ordering_card]
        grind only

theorem FreeMap.mem_FRan_add_one_cases (h : n + 1 ≤ brs.card) : x ∈ FRan (FreeMap (n + 1) brs) ↔ (x ∈ FRan (FreeMap n brs) ∨ x = FreeMap (n + 1) brs (Fin.last n)) := by
  apply Iff.intro
  · intro a
    simp [FRan, FreeMap] at a
    obtain ⟨i, hi⟩ := a
    induction i using Fin.lastCases with
    | cast j => apply Or.inl; subst hi; rw [FreeMap.FRan_def (Nat.le_of_succ_le h)]; simp [List.mem_take_iff_getElem]; use ↑j, (by grind); rw [@List.getD_getElem?]; simp; grind
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
    | inl h' => exact FreeMap.FRan_sub_add_one h h'
    | inr h' =>
      subst h'
      simp only [FRan.mem_def]

theorem FreeMap.inj_n  {brs : Finset α} (h : n ≤ brs.card) : (FreeMap n brs).Injective := by
  intro a₁ a₂ h'
  rw [FreeMap.fromIndex_brs_def h, FreeMap.fromIndex_brs_def h] at h'
  have := RelationSchema.fromIndex_inj.mp h'
  simp_all

theorem FreeMap.FRan_card_def (h : n ≤ brs.card) : (FRan (FreeMap n brs)).card = n :=
  FRan.card_def (inj_n h)

theorem FreeMap.get_def {brs : Finset α} {i : Fin n} {h : ↑i < (RelationSchema.ordering brs).length} :
  (FreeMap n brs) i = (RelationSchema.ordering brs)[i]'h := by
    simp only [FreeMap, RelationSchema.ordering, List.getD_eq_getElem?_getD, Fin.getElem_fin]
    rw [@List.getD_getElem?]
    split
    . simp
    . rw [← RelationSchema.ordering] at *; grind

theorem FreeMap.self_fromIndex_def (h' : n ≤ brs.card) :
  FreeMap (FRan (FreeMap n brs)).card brs (RelationSchema.index (RelationSchema.fromIndex_mem i)) = RelationSchema.fromIndex i := by
    have : (FRan (FreeMap n brs)).card ≤ n := by rw [FreeMap.FRan_card_def h']
    have : ↑i < brs.card := by grind
    rw [FreeMap, RelationSchema.index_fromIndex_eq, List.getD_eq_getElem?_getD, RelationSchema.fromIndex]
    simp_all only [RelationSchema.ordering_card, getElem?_pos, Option.getD_some,
      List.get_eq_getElem, FRan_ordering_def, Fin.coe_cast, List.getElem_take]

theorem FreeMap.self_def (h : a ∈ FRan (FreeMap n brs)) (h' : n ≤ brs.card) :
  FreeMap (FRan (FreeMap n brs)).card brs (RelationSchema.index h) = a := by
    have ⟨k, hk⟩ : ∃i : Fin (FRan (FreeMap n brs)).card, RelationSchema.fromIndex i = a := by use RelationSchema.index h; simp
    subst hk
    exact self_fromIndex_def h'

theorem FreeMap.index_self (h : FreeMap n brs i ∈ FRan (FreeMap n brs)) (h' : n ≤ brs.card) : (RelationSchema.index h) = i.cast (FRan_card_def h').symm := by
  rw [← RelationSchema.fromIndex_inj, RelationSchema.fromIndex_index_eq, ← self_fromIndex_def h', @RelationSchema.index_fromIndex_eq]
  rfl

theorem FreeMap.self_def_cast (h : a ∈ FRan (FreeMap n brs)) (h' : n ≤ brs.card) (h'' : n ≤ n') :
  FreeMap n' brs ((RelationSchema.index h).castLE (by rw [FreeMap.FRan_card_def h']; exact h'')) = a := by
    have ⟨k, hk⟩ : ∃i : Fin (FRan (FreeMap n brs)).card, RelationSchema.fromIndex i = a := by use RelationSchema.index h; simp
    subst hk
    exact self_fromIndex_def h'

theorem FreeMap.reverse_def {brs : Finset α} {i : Fin n} (h : n ≤ brs.card) : FreeMap n brs i = a ↔ (RelationSchema.fromIndex (i.castLE h)) = a := by
  rw [fromIndex_brs_def h]

theorem FRan.notMem_FreeMap_lift (h : n + 1 ≤ brs.card) : FreeMap (n + 1) brs (Fin.last n) ∉ FRan (FreeMap n brs) := by
  rw [FRan]
  simp only [Set.toFinset_range, FreeMap, Fin.val_last, List.getD_eq_getElem?_getD,
    List.getD_getElem?, RelationSchema.ordering_card, Finset.mem_image, Finset.mem_univ, true_and,
    not_exists]
  intro i
  have : n < brs.card := by grind
  simp only [this, ↓reduceDIte, ne_eq]
  have : ↑i < brs.card := by grind
  simp only [this, ↓reduceDIte, ne_eq]
  by_contra hc
  have := (RelationSchema.ordering_inj brs).mp hc
  grind
