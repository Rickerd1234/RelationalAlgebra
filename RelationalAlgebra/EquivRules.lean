import RelationalAlgebra.RelationalAlgebra

open RM

@[simp ←]
theorem projection_union {s' : RelationSchema} (inst1 inst2 : RelationInstance) (h_pr : s' ⊆ inst1.schema) (h_un : inst1.schema = inst2.schema):
  projection (union inst1 inst2 h_un) s' h_pr = union (projection inst1 s' h_pr) (projection inst2 s' (by rw [←h_un]; exact h_pr)) rfl := by
    unfold projection union
    simp_all only [Set.mem_union, RelationInstance.mk.injEq, true_and]
    simp_all only
    ext x : 1
    simp_all only [Set.mem_setOf_eq, Set.mem_union]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      simp_all only [not_false_eq_true, implies_true, and_true]
      cases left with
      | inl h =>
        apply Or.inl
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a a_1
            rfl
          }
          · simp_all only
      | inr h_1 =>
        apply Or.inr
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a a_1
            rfl
          }
          · simp_all only
    · intro a
      cases a with
      | inl h =>
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        simp_all only [not_false_eq_true, implies_true, and_true]
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a a_1
            rfl
          }
          · simp_all only [true_or]
      | inr h_1 =>
        obtain ⟨w, h⟩ := h_1
        obtain ⟨left, right⟩ := h
        simp_all only [not_false_eq_true, implies_true, and_true]
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            intro a a_1
            rfl
          }
          · simp_all only [or_true]
