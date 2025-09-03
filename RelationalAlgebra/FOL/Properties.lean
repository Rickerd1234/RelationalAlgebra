import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem BoundedQuery.relabel_attributesInQuery [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) :
  (φ.relabel g).attributesInQuery = (φ.attributesInQuery.pimage (λ a => (g a).getLeft?)) := by
    simp_all only [BoundedQuery.attributesInQuery, BoundedQuery.relabel_formula, BoundedFormula.relabel_freeVarFinset, Finset.pimage]

@[simp]
theorem BoundedQuery.relabel_isWellTyped [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (h : φ.isWellTyped) :
  (φ.relabel g).isWellTyped := by
    induction φ with
    | R dbs rn t => aesop

    | tEq t₁ t₂ =>
      simp_all only [isWellTyped.tEq_def, relabel.tEq_def, fol.Term.relabel_varFinsetLeft_relabelAux,
        isWellTyped.schema_eq_attributesInQuery, relabel_attributesInQuery, true_and, forall_const]
      obtain ⟨left, right⟩ := h
      simp_all only [isWellTyped.schema_eq_attributesInQuery]
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

    | and q₁ q₂ q₁_ih q₂_ih => aesop

    | ex q q_ih => aesop

@[simp]
theorem BoundedQuery.relabel_schema [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (h : φ.isWellTyped) :
  (φ.relabel g).schema = (φ.schema.pimage (λ a => (g a).getLeft?)) := by
    aesop
