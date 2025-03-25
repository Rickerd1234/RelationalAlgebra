import RelationalAlgebra.RelationalAlgebra

open RM

@[simp ←]
theorem projection_union {s1 s2 : RelationSchema} (inst1 inst2 : RelationInstance s1) (h : s2 ⊆ s1):
  projection (union inst1 inst2) s2 h = union (projection inst1 s2 h) (projection inst2 s2 h) :=
    Set.ext λ _ => ⟨ -- Proof by extensionality
      -- w ∈ projection (union inst1 inst2) s2 h → w ∈ union (projection inst1 s2 h) (projection inst2 s2 h)
      (λ ⟨w, hw_union, hw_project⟩ => Or.elim hw_union (λ w_in_1 => Or.inl ⟨w, w_in_1, hw_project⟩) (λ w_in_2 => Or.inr ⟨w, w_in_2, hw_project⟩)),
      -- w ∈ union (projection inst1 s2 h) (projection inst2 s2 h) → w ∈ projection (union inst1 inst2) s2 h
      (λ hx => Or.elim hx (λ ⟨w, w_in_1, w_project⟩ => ⟨w, Or.inl w_in_1, w_project⟩) (λ ⟨w, w_in_2, w_project⟩ => ⟨w, Or.inr w_in_2, w_project⟩))
    ⟩
