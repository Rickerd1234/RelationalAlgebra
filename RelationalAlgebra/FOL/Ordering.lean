import RelationalAlgebra.RelationalModel

import Mathlib.Data.Finset.Sort

namespace RM

section order

-- Add ordering to Attribute
instance Attribute.instLe : IsTrans Attribute (.≤.) where
  trans {_ _ _: Attribute} := Nat.le_trans

instance Attribute.instAntisymm : IsAntisymm Attribute (.≤.) where
  antisymm {_ _: Attribute} := Nat.le_antisymm

instance Attribute.instTotal : IsTotal Attribute (.≤.) where
  total := Nat.le_total

-- Add ordering to RelationSchema
def RelationSchema.ordering (rs : RelationSchema) : List Attribute
  := rs.sort (.≤.)

-- Proof usefull properties for ordering
@[simp]
theorem RelationSchema.ordering_mem (a : Attribute) (rs : RelationSchema) : a ∈ rs.ordering ↔ a ∈ rs:= by simp [ordering]

@[simp]
theorem RelationSchema.ordering_card (rs : RelationSchema) : rs.ordering.length = rs.card := by simp [ordering]

-- Add index? to RelationSchema
def RelationSchema.index? (rs : RelationSchema) (att : Attribute) : Option (Fin rs.card) :=
  (rs.ordering.finIdxOf? att).map (λ x : Fin (rs.ordering.length) => ⟨x, by simp [← RelationSchema.ordering_card]⟩)

-- Proof usefull properties for index?
@[simp]
theorem RelationSchema.index?_isSome {rs : RelationSchema} {att : Attribute} : (h : att ∈ rs) → (rs.index? att).isSome := by
  simp [← RelationSchema.ordering_mem, RelationSchema.index?]
  induction (RelationSchema.ordering rs) with
  | nil =>
    intro h
    simp_all only [List.not_mem_nil]
  | cons a as tail_ih =>
    intro h
    simp_all only [List.mem_cons, List.length_cons, List.finIdxOf?_cons, beq_iff_eq, Fin.zero_eta]
    cases h with
    | inl att_is_a => simp_all only [att_is_a, ↓reduceIte, Option.isSome_some]
    | inr h_2 =>
      simp_all only [forall_const]
      split
      next h => simp_all only [h, Option.isSome_some]
      next h => simp_all only [Option.isSome_map']

-- Add index to RelationSchema
def RelationSchema.index {rs : RelationSchema} {att : Attribute} (h : att ∈ rs) : Fin rs.card :=
  (RelationSchema.index? rs att).get (RelationSchema.index?_isSome h)

-- Proof usefull properties for index
@[simp]
theorem RelationSchema.index_lt_card {rs : RelationSchema} {att : Attribute} : (h : att ∈ rs) → rs.index h < rs.card := by
  simp [RelationSchema.ordering_mem, RelationSchema.index, RelationSchema.index?]

-- Add fromIndex to RelationSchema
def RelationSchema.fromIndex {rs : RelationSchema} (i : Fin rs.card) : Attribute := rs.ordering.get ⟨i, by simp [RelationSchema.ordering]⟩

-- Proof usefull properties for fromIndex
@[simp]
theorem RelationSchema.fromIndex_mem {rs : RelationSchema} : (i : Fin rs.card) → rs.fromIndex i ∈ rs := by
  intro i
  apply (RelationSchema.ordering_mem (Finset.sort (fun x1 x2 ↦ x1 ≤ x2) rs)[i] rs).mp
  simp [RelationSchema.ordering]

end order
