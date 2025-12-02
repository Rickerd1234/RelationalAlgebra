import RelationalAlgebra.RA.RelationalAlgebra

open RM


@[simp]
theorem joinSingleT.restrict (t : α →. μ) {h : rs ⊆ t.Dom} :
  joinSingleT t (t.restrict h) t := by
    simp_all only [joinSingleT, Set.mem_union]
    intro a
    simp_all only [PFun.mem_dom, PFun.mem_restrict, exists_and_left, and_imp, forall_exists_index, implies_true,
      not_or, not_and, not_exists, true_and]
    apply And.intro
    · intro a_1 x h_1
      ext a_2 : 1
      simp_all only [PFun.mem_restrict, true_and]
    · intro a_1 a_2
      simp_all only [not_false_eq_true, implies_true]
      ext a_1 : 1
      simp_all only [Part.notMem_none]

-- Projection over union
@[simp ←]
theorem projectionT_unionT {rs : Finset α} (ts1 ts2 : Set (α →. μ)) :
  projectionT (unionT ts1 ts2) rs = unionT (projectionT ts1 rs) (projectionT ts2 rs) := by
    simp_all only [projectionT, unionT, Set.mem_union]
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
