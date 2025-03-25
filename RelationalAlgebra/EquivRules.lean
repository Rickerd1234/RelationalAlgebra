import RelationalAlgebra.RelationalAlgebra

open RM

@[simp ←]
theorem projection_union {s1 s2 : RelationSchema} (inst1 inst2 : RelationInstance s1) (h : s2 ⊆ s1):
  projection (union inst1 inst2) s2 h = union (projection inst1 s2 h) (projection inst2 s2 h) := by
    simp [projection, union]
    ext x : 1
    simp_all only [Set.mem_setOf_eq, Set.mem_union]
    apply Iff.intro
    · intro a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      simp_all only
      cases left with
      | inl h_1 =>
        apply Or.inl
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a b
            rfl
          }
          · simp_all only
      | inr h_2 =>
        apply Or.inr
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a b
            rfl
          }
          · simp_all only
    · intro a
      cases a with
      | inl h_1 =>
        obtain ⟨w, h_1⟩ := h_1
        obtain ⟨left, right⟩ := h_1
        simp_all only
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a b
            rfl
          }
          · simp_all only [true_or]
      | inr h_2 =>
        obtain ⟨w, h_1⟩ := h_2
        obtain ⟨left, right⟩ := h_1
        simp_all only
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a b
            rfl
          }
          · simp_all only [or_true]
