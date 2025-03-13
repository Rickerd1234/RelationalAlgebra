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

theorem rename_id {s : RelationSchema} (inst : RelationInstance s):
  rename inst id = inst := by
    -- Proof using witness
    apply Set.ext
    intro t

    constructor
    -- w ∈ rename inst id → w ∈ inst
    · intro h
      obtain ⟨t', ⟨hl, hr⟩⟩ := h
      rw [← hr] at hl
      simp only [Function.comp_id] at hl
      exact hl

    -- w ∈ inst → w ∈ rename inst id
    · intro h
      use t
      simp only [Function.comp_id, and_self, and_true]
      exact h

theorem rename_inv {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s) (c : g ∘ f = id) :
  rename (rename inst f) g = inst := by
    -- Proof using witness
    apply Set.ext
    intro t

    constructor
    -- t ∈ rename (rename inst f) g → t ∈ inst
    · intro h
      -- Unpack existence from renames
      obtain ⟨_, ht', hg⟩ := h
      obtain ⟨_, ht'', hf⟩ := ht'

      -- Rewrite and simplify
      subst hf hg
      rw [Function.comp_assoc, c, Function.comp_id] at ht''
      exact ht''

    -- t ∈ inst → t ∈ rename (rename inst f) g
    · intro h
      unfold rename
      simp only [exists_eq_right', Set.mem_setOf_eq]
      rw [Function.comp_assoc, c, Function.comp_id]
      exact h

@[simp]
theorem rename_comp {s s' s'' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s'') (h : s → s'') (c : g ∘ f = h) :
  rename (rename inst f) g = rename inst h := by
    unfold rename at *
    subst c
    simp_all only [exists_eq_right', Set.mem_setOf_eq]
    rfl
