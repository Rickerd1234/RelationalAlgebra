import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Coercions

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
      (∀ a : ↑(s1 ∩ s2), t1 a = t2 a) ∧
      -- Attributes in s1
      (∀ a : s1, t a = t1 a) ∧
      -- Attributes in s2
      (∀ a : s2, t a = t2 a)
    }

theorem join_empty {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 (∅ : RelationInstance s2) = (∅ : RelationInstance (s1 ∪ s2)) := by
    unfold join
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, false_and, and_false, exists_const, Set.setOf_false]

theorem join_comm {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) (inst2 : RelationInstance s2) :
  join inst1 inst2 = join inst2 inst1 := by sorry

theorem join_self {s1 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 inst1 = inst1 := by sorry

end join
