import RelationalAlgebra.RelationalModel
import Mathlib.Data.Set.Basic

open RM

-- Coercion for relation schema union (construction)
@[simp]
def schema_union_right (α β : RelationSchema) : α → { a // a ∈ α ∪ β } := by
  intro a
  obtain ⟨val, property⟩ := a
  exact Subtype.mk val (Or.inl property)

instance schema_union_right_cast {α β : RelationSchema} :
  Coe α {a // a ∈ α ∪ β} := ⟨schema_union_right α β⟩

-- Coercion for relation schema union commutativity
@[simp]
def schema_union_comm (α β : RelationSchema) : {a // a ∈ α ∪ β} ≃ {a // a ∈ β ∪ α} := by rw [Set.union_comm]

instance schema_union_comm_cast (α β : RelationSchema) : Coe {a // a ∈ α ∪ β} {a // a ∈ β ∪ α} := ⟨schema_union_comm α β⟩

-- Coercion for relation instance schema union commutativity
@[simp]
def instance_union_comm_equiv (s1 s2 : RelationSchema) :
  RelationInstance (s1 ∪ s2) ≃ RelationInstance (s2 ∪ s1) := by rw [Set.union_comm]

instance instance_union_comm_cast (s1 s2 : RelationSchema) :
  Coe (RelationInstance (s1 ∪ s2)) (RelationInstance (s2 ∪ s1)) := ⟨instance_union_comm_equiv s1 s2⟩


-- Coercion for relation schema intersection (destruction)
@[simp]
noncomputable def schema_inter_left {α β : RelationSchema} (a : {a // a ∈ α ∩ β}) : α :=
  ⟨a.val, Set.mem_of_mem_inter_left a.property⟩

@[simp]
noncomputable def schema_inter_right {α β : RelationSchema} (a : {a // a ∈ α ∩ β}) : β :=
  ⟨a.val, Set.mem_of_mem_inter_right a.property⟩


noncomputable instance schema_inter_left_cast (α β : RelationSchema) :
  CoeOut {a // a ∈ α ∩ β} α where
  coe := schema_inter_left

noncomputable instance schema_inter_right_cast (α β : RelationSchema) :
  CoeOut {a // a ∈ α ∩ β} β where
  coe := schema_inter_right

-- Coercion for relation schema intersection commutativity
@[simp]
def schema_inter_comm (α β : RelationSchema) : {a // a ∈ α ∩ β} ≃ {a // a ∈ β ∩ α} := by rw [Set.inter_comm]

instance schema_inter_comm_cast (α β : RelationSchema) : Coe {a // a ∈ α ∩ β} {a // a ∈ β ∩ α} := ⟨schema_inter_comm α β⟩
