import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem BoundedQuery.relabel_attributesInQuery [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) :
  (φ.relabel g).attributesInQuery = (φ.attributesInQuery.pimage (λ a => (g a).getLeft?)) := by
    simp_all only [BoundedQuery.attributesInQuery, BoundedQuery.relabel_formula, BoundedFormula.relabel_freeVarFinset, Finset.pimage]

@[simp]
theorem BoundedQuery.relabel_schema [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (h : φ.isWellTyped) :
  (φ.relabel g).schema = (φ.schema.pimage (λ a => (g a).getLeft?)) := by
    simp_all only [BoundedQuery.schema, BoundedQuery.attributesInQuery, BoundedQuery.relabel_formula, BoundedFormula.relabel_freeVarFinset, Finset.pimage]
    ext a
    induction φ
    . sorry
    . aesop
    . sorry
    . aesop

@[simp]
theorem BoundedQuery.relabel_isWellTyped [folStruc] {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (h : φ.isWellTyped) :
  (φ.relabel g).isWellTyped := by
    induction φ with
    | R dbs rn t =>
      simp_all

    | tEq t₁ t₂ =>
      simp_all

    | and q₁ q₂ q₁_ih q₂_ih =>
      by_cases h' : q₁.isWellTyped ∧ q₂.isWellTyped
      . simp_all only [relabel.and_def, forall_const, isWellTyped.and_from_both, isWellTyped.and_comm]
      . simp_all
        sorry

    | ex q q_ih => simp_all
