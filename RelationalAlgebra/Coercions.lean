import RelationalAlgebra.RelationalModel
import Mathlib.Data.Set.Basic

open RM

-- Coercion for relation schema union (construction)
@[simp]
def schema_union_right (s1 s2 : RelationSchema) : s1 → {a // a ∈ s1 ∪ s2} := by
  intro a
  obtain ⟨val, property⟩ := a
  exact Subtype.mk val (Or.inl property)

instance schema_union_right_cast {s1 s2 : RelationSchema} :
  Coe s1 {a // a ∈ s1 ∪ s2} := ⟨schema_union_right s1 s2⟩

-- Coercion for relation schema union commutativity
@[simp]
def schema_union_comm (s1 s2 : RelationSchema) : {a // a ∈ s1 ∪ s2} ≃ {a // a ∈ s2 ∪ s1} := by rw [Set.union_comm]

instance schema_union_comm_cast (s1 s2 : RelationSchema) : Coe {a // a ∈ s1 ∪ s2} {a // a ∈ s2 ∪ s1} := ⟨schema_union_comm s1 s2⟩

-- Coercion for relation instance schema union commutativity
@[simp]
def instance_union_comm (s1 s2 : RelationSchema) : RelationInstance (s1 ∪ s2) ≃ RelationInstance (s2 ∪ s1) := by rw [Set.union_comm]

instance instance_union_comm_cast (s1 s2 : RelationSchema) :
  Coe (RelationInstance (s1 ∪ s2)) (RelationInstance (s2 ∪ s1)) := ⟨instance_union_comm s1 s2⟩

-- Coercion for relation instance schema union self
def instance_union_self (s1 : RelationSchema) : RelationInstance (s1 ∪ s1) ≃ RelationInstance s1 := by rw [Set.union_self]

instance instance_union_self_cast (s1 : RelationSchema) : CoeOut (RelationInstance (s1 ∪ s1)) (RelationInstance s1) := ⟨instance_union_self s1⟩

-- Coercion for relation schema intersection (destruction)
@[simp]
noncomputable def schema_inter_left {s1 s2 : RelationSchema} (a : {a // a ∈ s1 ∩ s2}) : s1 :=
  ⟨a.val, Set.mem_of_mem_inter_left a.property⟩

@[simp]
noncomputable def schema_inter_right {s1 s2 : RelationSchema} (a : {a // a ∈ s1 ∩ s2}) : s2 :=
  ⟨a.val, Set.mem_of_mem_inter_right a.property⟩

noncomputable instance schema_inter_left_cast (s1 s2 : RelationSchema) :
  CoeOut {a // a ∈ s1 ∩ s2} s1 where
  coe := schema_inter_left

noncomputable instance schema_inter_right_cast (s1 s2 : RelationSchema) :
  CoeOut {a // a ∈ s1 ∩ s2} s2 where
  coe := schema_inter_right

-- Coercion for relation schema intersection commutativity
@[simp]
def schema_inter_comm (s1 s2 : RelationSchema) : {a // a ∈ s1 ∩ s2} ≃ {a // a ∈ s2 ∩ s1} := by rw [Set.inter_comm]

instance schema_inter_comm_cast (s1 s2 : RelationSchema) : Coe {a // a ∈ s1 ∩ s2} {a // a ∈ s2 ∩ s1} := ⟨schema_inter_comm s1 s2⟩
