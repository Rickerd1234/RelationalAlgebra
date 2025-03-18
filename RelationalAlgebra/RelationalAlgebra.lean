import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Equiv

open RM

-- Union
section union

def union {s : RelationSchema} (inst inst' : RelationInstance s) : RelationInstance s := inst ∪ inst'

@[simp]
theorem union_empty {s : RelationSchema} (inst : RelationInstance s) :
  union inst ∅ = inst := Set.union_empty inst

@[simp]
theorem union_comm {s : RelationSchema} (inst inst' : RelationInstance s) :
  union inst inst' = union inst' inst := by exact Set.union_comm inst inst'

end union


-- Rename
section rename

def rename {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') : RelationInstance s' := { t' | ∃ t ∈ inst, t' ∘ f = t }

@[simp]
theorem rename_id {s : RelationSchema} (inst : RelationInstance s):
  rename inst id = inst := by simp only [rename, Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem rename_comp {s s' s'' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s'') (h : s → s'') (c : g ∘ f = h) :
  rename (rename inst f) g = rename inst h := by simp only [rename, exists_eq_right', Set.mem_setOf_eq, Function.comp_assoc, c]

@[simp]
theorem rename_inv {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s) (c : g ∘ f = id) :
  rename (rename inst f) g = inst := by simp only [rename_comp, c, rename_id]

end rename


-- Join
section join

def join {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) (inst2 : RelationInstance s2) :
  RelationInstance (s1 ∪ s2) :=
    { t | ∃ t1 ∈ inst1, ∃ t2 ∈ inst2,
      -- Attributes in both s1 and s2
      (∀ a : ↑(s1 ∩ s2), t1 ⟨a, Set.mem_of_mem_inter_left a.prop⟩ = t2 ⟨a, Set.mem_of_mem_inter_right a.prop⟩) ∧
      -- Attributes in s1
      (∀ a : s1, t ⟨a, Or.inl a.prop⟩  = t1 a) ∧
      -- Attributes in s2
      (∀ a : s2, t ⟨a, Or.inr a.prop⟩  = t2 a)
    }

theorem join_empty {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 (∅ : RelationInstance s2) = (∅ : RelationInstance (s1 ∪ s2)) := by
    simp only [join, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

theorem empty_join {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) :
  join (∅ : RelationInstance s2) inst1 = (∅ : RelationInstance (s2 ∪ s1)) := by
    simp only [join, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

theorem join_comm {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) (inst2 : RelationInstance s2) :
  join inst1 inst2 = (instance_equiv schema_union_comm) (join inst2 inst1) := by
    simp [join, instance_equiv, tuple_equiv]
    ext t
    simp_all only [Set.mem_setOf_eq, Set.mem_image]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right⟩ := right
      use tuple_equiv schema_union_comm t
      apply And.intro
      · apply Exists.intro
        · apply And.intro
          · exact left_1
          · apply Exists.intro
            · apply And.intro
              · exact left
              · simp_all only [and_self, implies_true, true_and]
                apply And.intro
                · intro a b
                  apply right
                · intro a b
                  apply left_3
      · rfl
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := left
      obtain ⟨left, right_1⟩ := h
      obtain ⟨w_2, h⟩ := right_1
      obtain ⟨left_1, right_1⟩ := h
      obtain ⟨left_2, right_1⟩ := right_1
      obtain ⟨left_3, right_1⟩ := right_1
      subst right
      simp_all only
      apply Exists.intro
      · apply And.intro
        · exact left_1
        · apply Exists.intro
          · apply And.intro
            · exact left
            · simp_all only [and_self, implies_true, true_and]
              apply And.intro
              · intro a b
                apply right_1
              · intro a b
                apply left_3

theorem join_self {s1 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 inst1 = (instance_equiv schema_union_self) inst1 := by
    simp [join, instance_equiv, tuple_equiv, schema_union_self]
    ext t
    simp_all only [Set.mem_setOf_eq, Set.mem_image]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right⟩ := right
      simp_all only [implies_true]
      use tuple_equiv schema_union_self.symm t
      apply And.intro
      · simp [tuple_equiv, schema_union_self]
        simp_all only [Subtype.coe_prop, Subtype.coe_eta]
      · rfl
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only
      apply Exists.intro
      · apply And.intro
        · exact left
        · simp_all only [implies_true, true_and, and_self]
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {
              intro a b
              rfl
            }
            · simp_all only

end join
