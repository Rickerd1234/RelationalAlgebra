import RelationalAlgebra.RelationalModel

import Mathlib.Data.Finset.Sort

namespace RM

variable {α μ : Type}
section order

variable [LinearOrder α]

/--
Define ordering for 'RelationSchema'.
Required to convert between named Relational Model and unnamed `ModelTheory`
-/
def RelationSchema.ordering (rs : Finset α) : List α
  := rs.sort (.≤.)

-- Proof usefull properties for ordering
@[simp]
theorem RelationSchema.ordering_mem (a : α) (rs : Finset α) : a ∈ ordering rs ↔ a ∈ rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_nil_iff_empty (rs : Finset α) : ordering rs = [] ↔ rs = ∅:= by
  simp only [List.eq_nil_iff_forall_not_mem, ordering_mem, Finset.eq_empty_iff_forall_notMem]

@[simp]
theorem RelationSchema.ordering_eq_empty : ordering (∅ : Finset α) = [] := by
  simp only [ordering_nil_iff_empty]

@[simp]
theorem RelationSchema.ordering_head?_self_notEmpty {rs : Finset α} (h : rs ≠ ∅) : (ordering rs).head?.getD a ∈ rs := by
  simp_all [Option.getD]
  split
  next opt x heq =>
    simp [List.head?_eq_some_iff] at heq
    obtain ⟨w, h_1⟩ := heq
    exact (RelationSchema.ordering_mem x rs).mp (by simp only [h_1, List.mem_cons, true_or])
  next opt heq =>
    simp_all only [List.head?_eq_none_iff, ordering_nil_iff_empty]

@[simp]
theorem RelationSchema.ordering_head?_self_mem {rs : Finset α} (h : a ∈ rs) : (ordering rs).head?.getD a' ∈ rs := by
  apply ordering_head?_self_notEmpty
  simp_all [← Finset.nonempty_iff_ne_empty, Finset.nonempty_def]
  use a

@[simp]
theorem RelationSchema.ordering_eq_toFinset (rs : Finset α) [DecidableEq α] : (ordering rs).toFinset = rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_nodup (rs : Finset α) [DecidableEq α] : List.Nodup (ordering rs) := by simp [ordering]

@[simp]
theorem RelationSchema.ordering_inj (rs : Finset α) {i j : Fin (ordering rs).length}
  : (ordering rs).get i = (ordering rs).get j ↔ i = j := by
    simp_all [ordering]
    apply Iff.intro
    · intro a
      apply (List.Nodup.get_inj_iff ?_).mp a
      simp_all only [Finset.sort_nodup]
    · intro a
      subst a
      simp_all only

@[simp]
theorem RelationSchema.ordering_card (rs : Finset α) : (ordering rs).length = rs.card := by simp [ordering]

-- Add index? to RelationSchema
variable [BEq α] {rs : Finset α}

/-- Get the index of an attribute `att` in a specific schema `rs`, `.none` if not contained. -/
def RelationSchema.index? (rs : Finset α) (att : α) : Option (Fin rs.card) :=
  ((ordering rs).finIdxOf? att).map (λ x : Fin ((ordering rs).length) => x.cast (RelationSchema.ordering_card rs))

-- Proof usefull properties for index?
@[simp]
theorem RelationSchema.index?_isSome [LawfulBEq α] : (index? rs att).isSome ↔ att ∈ rs := by
  simp [← RelationSchema.ordering_mem, RelationSchema.index?]

@[simp]
theorem RelationSchema.index?_isSome_eq_iff : (index? rs att).isSome ↔ ∃i, index? rs att = .some i := by
  simp_all only [@Option.isSome_iff_exists]

@[simp]
theorem RelationSchema.index?_none [LawfulBEq α] : index? rs att = .none ↔ att ∉ rs := by
  rw [index?, Option.map_eq_none_iff, List.finIdxOf?_eq_none_iff, ← ordering_mem]

/-- Get the index of an attribute `att` in a specific schema `rs`, given `att ∈ rs`. -/
def RelationSchema.index [LawfulBEq α] (h : att ∈ rs) : Fin rs.card :=
  (RelationSchema.index? rs att).get (index?_isSome.mpr h)

@[simp]
theorem RelationSchema.index?_eq_index_if_mem [LawfulBEq α] (h : att ∈ rs) : (index? rs att) = .some (index h) := by
  simp [index]

-- Proof usefull properties for index
@[simp]
theorem RelationSchema.index_lt_card [LawfulBEq α] (h : att ∈ rs) : index h < rs.card := by
  simp only [Fin.is_lt]

/-- Get the attribute for a specific index (`i: Fin rs.card`) in a relation schema `rs`. -/
def RelationSchema.fromIndex [LawfulBEq α] (i : Fin rs.card) : α := (ordering rs).get (i.cast (ordering_card rs).symm)

-- Proof usefull properties for fromIndex
theorem RelationSchema.fromIndex_eq_get [LawfulBEq α] (i : ℕ) (h : i < (ordering rs).length) : (RelationSchema.ordering rs)[i]'h = fromIndex ⟨i, by simp_all; apply h⟩  := by
  simp [fromIndex]

@[simp]
theorem RelationSchema.fromIndex_mem [LawfulBEq α] (i : Fin rs.card) : fromIndex i ∈ rs := by
  apply (RelationSchema.ordering_mem (Finset.sort (.≤.) rs)[i] rs).mp
  simp [RelationSchema.ordering]

@[simp]
theorem RelationSchema.fromIndex_Dom [LawfulBEq α] {dbi : DatabaseInstance ρ α μ} (h : t ∈ (dbi.relations rn).tuples) (i : Fin (dbi.schema rn).card) : (t (fromIndex i)).Dom := by
  have z := (dbi.relations rn).validSchema t h
  rw [dbi.validSchema rn] at z
  have z'' : fromIndex i ∈ t.Dom := by simp_all
  exact z''

-- Proof uniqueness/injectivity for fromIndex and index functions
theorem RelationSchema.fromIndex_inj [LawfulBEq α] {i j : Fin rs.card} : fromIndex i = fromIndex j ↔ i = j := by
  apply Iff.intro
  · intro a
    unfold fromIndex at a
    simp_all only [List.get_eq_getElem]
    have z := (RelationSchema.ordering_inj rs).mp a
    simp_all only [Fin.coe_cast, Fin.mk.injEq]
    ext : 1
    simp_all only
  · intro a
    subst a
    simp_all only

@[simp]
theorem RelationSchema.index?_inj [LawfulBEq α] : index? rs i = index? rs j ↔ i = j ∨ i ∉ rs ∧ j ∉ rs := by
  apply Iff.intro
  · intro a
    by_cases h : (index? rs i).isSome
    . simp_all only
      refine Or.inl ?_
      simp_all only [index?_isSome_eq_iff]
      obtain ⟨w, h⟩ := h
      simp_all only
      unfold index? at *
      aesop
    . simp_all only [index?_isSome, ← index?_none, and_self, or_true]
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only
    | inr h_1 =>
      obtain ⟨left, right⟩ := h_1
      simp_all only [← index?_none]

@[simp]
theorem RelationSchema.index?_inj_mem [LawfulBEq α]  (h1 : i ∈ rs) (h2 : j ∈ rs) : index? rs i = index? rs j ↔ i = j := by
  simp_all only [index?_inj, not_true_eq_false, and_self, or_false]

@[simp]
theorem RelationSchema.index_inj [LawfulBEq α] (h1 : i ∈ rs) (h2 : j ∈ rs) : index h1 = index h2 ↔ i = j := by
  apply Iff.intro
  · intro a
    unfold index at *
    simp_all [Option.get]
    split at a
    rename_i x x_1 x_2 x_3 heq heq_1
    split at a
    rename_i x_4 x_5 x_6 x_7 heq_2 heq_3
    subst a
    simp_all only [heq_eq_eq]
    simp_all only [Option.isSome_some]
    apply (index?_inj_mem h1 h2).mp
    simp_all only
  · intro a
    subst a
    simp_all only


@[simp]
theorem RelationSchema.index_fromIndex_inj [LawfulBEq α] {i j : Fin rs.card} : index? rs (fromIndex i) = index? rs (fromIndex j) ↔ i = j := by
  simp_all only [index?_inj, fromIndex_mem, not_true_eq_false, and_self, or_false]
  apply Iff.intro
  · intro a
    exact fromIndex_inj.mp a
  · intro a
    subst a
    simp_all only


@[simp]
theorem RelationSchema.fromIndex_index_inj [LawfulBEq α] (h1 : att1 ∈ rs) (h2 : att2 ∈ rs) : fromIndex (index h1) = fromIndex (index h2) ↔ att1 = att2 := by
  apply Iff.intro
  · intro a
    exact (index_inj h1 h2).mp (fromIndex_inj.mp a)
  · intro a
    subst a
    simp_all only

@[simp]
theorem RelationSchema.fromIndex_index_eq [LawfulBEq α] (h : att ∈ rs) : fromIndex (index h) = att := by
  unfold fromIndex index index? List.finIdxOf? Option.map Option.get
  simp_all only [Option.isSome_some, List.get_eq_getElem, Fin.coe_cast]
  split
  rename_i x x_1 x_2 x_3 heq heq_1
  simp_all only [heq_eq_eq]
  split at heq
  next opt x_4
    heq_1 =>
    simp_all only [List.findFinIdx?_eq_some_iff, Fin.getElem_fin, beq_iff_eq, Option.some.injEq]
    subst heq
    simp_all only [Fin.coe_cast]
  next opt heq_1 => simp_all only [List.findFinIdx?_eq_none_iff, beq_iff_eq, reduceCtorEq]

@[simp]
theorem RelationSchema.index_fromIndex_eq [LawfulBEq α] (i : Fin rs.card) : index (fromIndex_mem i) = i := by
  unfold fromIndex index index? List.finIdxOf? Option.map Option.get
  simp_all only [Option.isSome_some, List.get_eq_getElem, Fin.coe_cast]
  induction i
  simp_all only
  split
  rename_i x x_1 x_2 x_3 heq heq_1
  simp_all only [Fin.cast_mk, List.get_eq_getElem, heq_eq_eq]
  simp_all only [Option.isSome_some]
  split at heq
  next opt x_3
    heq_1 =>
    simp_all only [List.findFinIdx?_eq_some_iff, Fin.getElem_fin, beq_iff_eq, Option.some.injEq]
    subst heq
    obtain ⟨left, right⟩ := heq_1
    simp [Option.isSome_iff_exists] at x_1
    exact index_fromIndex_inj.mp (congrArg (index? rs) left)
  next opt heq_1 =>
    simp_all only [List.findFinIdx?_eq_none_iff, ordering_mem, beq_iff_eq, Finset.forall_mem_not_eq', reduceCtorEq]


@[simp]
theorem RelationSchema.Dom_sub_fromIndex [LawfulBEq α] {dbi : DatabaseInstance ρ α μ} : {a | ∃(i : Fin (dbi.schema rn).card), a = fromIndex i} = dbi.schema rn := by
  ext a
  simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    subst h
    simp_all only [fromIndex_mem]
  · intro a_1
    use index a_1
    simp_all only [fromIndex_index_eq]

end order
