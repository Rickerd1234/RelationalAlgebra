import RelationalAlgebra.RelationalModel

import Mathlib.Data.Finset.Sort

namespace RM

section order

-- Add ordering to Attribute
instance Attribute.instLE : IsTrans Attribute (.≤.) where
  trans {_ _ _: Attribute} := String.le_trans

instance Attribute.instAntisymm : IsAntisymm Attribute (.≤.) where
  antisymm {_ _: Attribute} := String.le_antisymm

instance Attribute.instTotal : IsTotal Attribute (.≤.) where
  total := String.le_total

-- Add ordering to RelationSchema
def RelationSchema.ordering (rs : RelationSchema) : List Attribute
  := rs.sort (.≤.)

-- Proof usefull properties for ordering
@[simp]
theorem RelationSchema.ordering_mem (a : Attribute) (rs : RelationSchema) : a ∈ rs.ordering ↔ a ∈ rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_nil_iff_empty (rs : RelationSchema) : rs.ordering = [] ↔ rs = ∅:= by
  simp only [List.eq_nil_iff_forall_not_mem, ordering_mem, Finset.eq_empty_iff_forall_notMem]

@[simp]
theorem RelationSchema.ordering_eq_empty : (∅ : RelationSchema).ordering = [] := by
  simp only [ordering_nil_iff_empty]

@[simp]
theorem RelationSchema.ordering_head?_self_notEmpty {rs : RelationSchema} {a : Attribute} (h : rs ≠ ∅) : rs.ordering.head?.getD a ∈ rs := by
  simp_all [Option.getD]
  split
  next opt x heq =>
    simp [List.head?_eq_some_iff] at heq
    obtain ⟨w, h_1⟩ := heq
    exact (RelationSchema.ordering_mem x rs).mp (by simp only [h_1, List.mem_cons, true_or])
  next opt heq =>
    simp_all only [List.head?_eq_none_iff, ordering_nil_iff_empty]

@[simp]
theorem RelationSchema.ordering_head?_self_mem {rs : RelationSchema} {a a' : Attribute} (h : a ∈ rs) : rs.ordering.head?.getD a' ∈ rs := by
  apply ordering_head?_self_notEmpty
  simp_all [← Finset.nonempty_iff_ne_empty, Finset.nonempty_def]
  use a

@[simp]
theorem RelationSchema.ordering_eq_toFinset (rs : RelationSchema) : rs.ordering.toFinset = rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_nodup (rs : RelationSchema) : List.Nodup rs.ordering := by simp [ordering]

@[simp]
theorem RelationSchema.ordering_inj (rs : RelationSchema) {i j : Fin rs.ordering.length}
  : rs.ordering.get i = rs.ordering.get j ↔ i = j := by
    simp_all [ordering]
    apply Iff.intro
    · intro a
      apply (List.Nodup.get_inj_iff ?_).mp a
      simp_all only [Finset.sort_nodup]
    · intro a
      subst a
      simp_all only

@[simp]
theorem RelationSchema.ordering_card (rs : RelationSchema) : rs.ordering.length = rs.card := by simp [ordering]

-- Add index? to RelationSchema
def RelationSchema.index? (rs : RelationSchema) (att : Attribute) : Option (Fin rs.card) :=
  (rs.ordering.finIdxOf? att).map (λ x : Fin (rs.ordering.length) => x.cast (RelationSchema.ordering_card rs))

-- Proof usefull properties for index?
@[simp]
theorem RelationSchema.index?_isSome {rs : RelationSchema} {att : Attribute} : (rs.index? att).isSome ↔ att ∈ rs := by
  simp [← RelationSchema.ordering_mem, RelationSchema.index?]

@[simp]
theorem RelationSchema.index?_isSome_eq_iff {rs : RelationSchema} {att : Attribute} : (rs.index? att).isSome ↔ ∃i, rs.index? att = .some i := by
  simp_all only [@Option.isSome_iff_exists]

@[simp]
theorem RelationSchema.index?_none {rs : RelationSchema} {att : Attribute} : rs.index? att = .none ↔ att ∉ rs := by
  simp [← RelationSchema.ordering_mem, RelationSchema.index?]

-- Add index to RelationSchema
def RelationSchema.index {rs : RelationSchema} {att : Attribute} (h : att ∈ rs) : Fin rs.card :=
  (RelationSchema.index? rs att).get (index?_isSome.mpr h)

-- Proof usefull properties for index
@[simp]
theorem RelationSchema.index_lt_card {rs : RelationSchema} {att : Attribute} (h : att ∈ rs) : rs.index h < rs.card := by
  simp only [Fin.is_lt]

-- Add fromIndex to RelationSchema
def RelationSchema.fromIndex {rs : RelationSchema} (i : Fin rs.card) : Attribute := rs.ordering.get (i.cast (RelationSchema.ordering_card rs).symm)

-- Proof usefull properties for fromIndex
@[simp]
theorem RelationSchema.fromIndex_mem {rs : RelationSchema} (i : Fin rs.card) : rs.fromIndex i ∈ rs := by
  apply (RelationSchema.ordering_mem (Finset.sort rs (fun x1 x2 ↦ x1 ≤ x2))[i] rs).mp
  simp [RelationSchema.ordering]

@[simp]
theorem RelationSchema.fromIndex_Dom {dbi : DatabaseInstance} (h : t ∈ (dbi.relations rn).tuples) (i : Fin (dbi.schema rn).card) : (t ((dbi.schema rn).fromIndex i)).Dom := by
  have z := (dbi.relations rn).validSchema t h
  rw [dbi.validSchema rn] at z
  have z'' : fromIndex i ∈ t.Dom := by simp_all
  exact z''

-- Proof uniqueness/injectivity for fromIndex and index functions
theorem RelationSchema.fromIndex_inj {rs : RelationSchema} {i j : Fin rs.card} : RelationSchema.fromIndex i = RelationSchema.fromIndex j ↔ i = j := by
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
theorem RelationSchema.index?_inj {rs : RelationSchema} {i j : Attribute} : rs.index? i = rs.index? j ↔ i = j ∨ i ∉ rs ∧ j ∉ rs := by
  apply Iff.intro
  · intro a
    by_cases h : (rs.index? i).isSome
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
theorem RelationSchema.index?_inj_mem {rs : RelationSchema} {i j : Attribute} (h1 : i ∈ rs) (h2 : j ∈ rs) : rs.index? i = rs.index? j ↔ i = j := by
  aesop

@[simp]
theorem RelationSchema.index_inj {rs : RelationSchema} {i j : Attribute} (h1 : i ∈ rs) (h2 : j ∈ rs) : RelationSchema.index h1 = RelationSchema.index h2 ↔ i = j := by
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
theorem RelationSchema.index_fromIndex_inj {rs : RelationSchema} {i j : Fin rs.card} : rs.index? (RelationSchema.fromIndex i) = rs.index? (RelationSchema.fromIndex j) ↔ i = j := by
  simp_all only [index?_inj, fromIndex_mem, not_true_eq_false, and_self, or_false]
  apply Iff.intro
  · intro a
    exact fromIndex_inj.mp a
  · intro a
    subst a
    simp_all only


@[simp]
theorem RelationSchema.fromIndex_index_inj {att1 att2} {rs : RelationSchema} (h1 : att1 ∈ rs) (h2 : att2 ∈ rs) : RelationSchema.fromIndex (RelationSchema.index h1) = RelationSchema.fromIndex (RelationSchema.index h2) ↔ att1 = att2 := by
  apply Iff.intro
  · intro a
    exact (index_inj h1 h2).mp (fromIndex_inj.mp a)
  · intro a
    subst a
    simp_all only

@[simp]
theorem RelationSchema.fromIndex_index_eq {att} {rs : RelationSchema} (h : att ∈ rs) : RelationSchema.fromIndex (RelationSchema.index h) = att := by
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
theorem RelationSchema.index_fromIndex_eq {rs : RelationSchema} (i : Fin rs.card) : RelationSchema.index (RelationSchema.fromIndex_mem i) = i := by
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
    exact index_fromIndex_inj.mp (congrArg rs.index? left)
  next opt heq_1 =>
    simp_all only [List.findFinIdx?_eq_none_iff, ordering_mem, beq_iff_eq, Finset.forall_mem_not_eq', reduceCtorEq]


@[simp]
theorem RelationSchema.Dom_sub_fromIndex {dbi : DatabaseInstance} : {a | ∃(i : Fin (dbi.schema rn).card), a = RelationSchema.fromIndex i} = dbi.schema rn := by
  ext a
  simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    subst h
    simp_all only [fromIndex_mem]
  · intro a_1
    use (dbi.schema rn).index a_1
    simp_all only [fromIndex_index_eq]

end order
