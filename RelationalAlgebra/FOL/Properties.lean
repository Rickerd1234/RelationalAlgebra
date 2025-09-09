import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem BoundedQuery.relabel_schema [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) :
  (φ.relabel g).schema = (φ.schema.pimage (λ a => (g a).getLeft?)) := by
    induction φ with
    | R =>
      simp [Relations.boundedFormula]
      aesop
    | _ => aesop

@[simp]
theorem BoundedQuery.relabel_isWellTyped [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (h : φ.isWellTyped) :
  (φ.relabel g).isWellTyped := by
    induction φ with
    | tEq q t₁ t₂ =>
      simp_all only [isWellTyped.tEq_def, relabel.tEq_def,
        fol.Term.relabel_varFinsetLeft_relabelAux, relabel_schema, true_and, forall_const]
      obtain ⟨left, right⟩ := h
      apply Finset.subset_iff.mpr
      intro x a
      simp_all only [Finset.mem_union, Finset.mem_pimage, Part.mem_ofOption, Option.mem_def, Sum.getLeft?_eq_some_iff]
      cases a with
      | inl h =>
        obtain ⟨w, h⟩ := h
        obtain ⟨left_1, right_1⟩ := h
        apply Exists.intro
        · apply And.intro
          apply right
          on_goal 2 => {exact right_1
          }
          simp_all only [Finset.mem_union, true_or]
      | inr h_1 =>
        obtain ⟨w, h⟩ := h_1
        obtain ⟨left_1, right_1⟩ := h
        apply Exists.intro
        · apply And.intro
          apply right
          on_goal 2 => {exact right_1
          }
          simp_all only [Finset.mem_union, or_true]

    | _ => aesop

@[simp]
theorem BoundedQuery.relabel_isWellTyped_sumInl [folStruc] {n k} (g : Attribute → Attribute) (h : g.Bijective) (φ : BoundedQuery k) :
  (φ.relabel ((Sum.inl ∘ g) : Attribute → Attribute ⊕ Fin n)).isWellTyped → φ.isWellTyped := by
    induction φ with
    | tEq q t₁ t₂ q_ih =>
      simp_all
      intro a a_1
      simp_all only [forall_const, relabel_isWellTyped]
      obtain ⟨left, right⟩ := h
      rw [@Finset.union_subset_iff] at a_1 ⊢
      obtain ⟨left_1, right_1⟩ := a_1
      apply And.intro
      . exact (Finset.image_subset_image_iff left).mp left_1
      . exact (Finset.image_subset_image_iff left).mp right_1

    | _ => aesop
