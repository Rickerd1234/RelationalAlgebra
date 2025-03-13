import RelationalAlgebra.RelationalModel

theorem not_mem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b := Iff.rfl

-- Union
def union {relSch : RelationSchema} (relI relI' : RelationInstance relSch) : RelationInstance relSch := Set.union relI relI'

theorem union_comm {relSch : RelationSchema} (relI relI' : RelationInstance relSch) :
  union relI relI' = union relI' relI := by
    exact Set.union_comm relI relI'

-- Rename
def rename {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') : RelationInstance s' :=
  { t' | ∃ t ∈ inst, t' ∘ f = t}

@[simp]
theorem rename_id {s : RelationSchema} (inst : RelationInstance s):
  rename inst id = inst := by
    unfold rename
    simp only [Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem rename_comp {s s' s'' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s'') (h : s → s'') (c : g ∘ f = h) :
  rename (rename inst f) g = rename inst h := by
    unfold rename at *
    subst c
    simp_all only [exists_eq_right', Set.mem_setOf_eq]
    rfl

@[simp]
theorem rename_inv {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s) (c : g ∘ f = id) :
  rename (rename inst f) g = inst := by
    simp only [rename_comp, c, rename_id]
