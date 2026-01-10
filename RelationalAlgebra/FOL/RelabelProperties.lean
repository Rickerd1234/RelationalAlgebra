import RelationalAlgebra.FOL.Relabel
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

namespace FOL

variable {ρ α : Type} {dbs : ρ → Finset α}

/-- `Term.relabel g` maintains injectivity of `g`. -/
@[simp]
theorem relabel.Injective_def {k n : ℕ} {g : (α ⊕ Fin k) → (α ⊕ Fin n)} (h : g.Injective) :
  Function.Injective (Term.relabel g : (fol dbs).Term (α ⊕ Fin k) → (fol dbs).Term (α ⊕ Fin n)) := by
    simp_all [Function.Injective]
    intros t₁ t₂ h'
    have ⟨t₁, ht₁⟩ := Term.cases t₁
    have ⟨t₂, ht₂⟩ := Term.cases t₂
    subst ht₁ ht₂
    simp_all only [relabel, var.injEq]
    obtain ⟨left, right⟩ := h
    cases t₁ with
    | inl val =>
      cases t₂ with
      | inl val_1 =>
        simp_all only [Sum.inl.injEq]
        exact (left val).1 val_1 h'
      | inr val_2 => simp_all only
    | inr val_1 =>
      cases t₂ with
      | inl val => simp_all only
      | inr val_2 =>
        simp_all only [Sum.inr.injEq]
        exact (right val_1).2 val_2 h'

/-- `BoundedFormula.relabelAux g _` maintains injectivity of `g`. -/
@[simp]
theorem relabel.Injective_relabelAux {k n : ℕ} {g : String → (String ⊕ Fin n)} (h : g.Injective) :
  Function.Injective (BoundedFormula.relabelAux g k) := by
    simp_all [Function.Injective]
    apply And.intro
    · intro a
      apply And.intro
      · intro a_1 a_2
        by_cases h' : (g a_1).isLeft
        . simp_all [Sum.isLeft_iff]
          nth_rewrite 2 [BoundedFormula.relabelAux] at a_2
          simp_all only [Function.comp_apply, Sum.map_inl]
          obtain ⟨w, h_1⟩ := h'
          simp_all only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, id_eq, fol.Term.relabelAux_sumInl]
          apply h
          simp_all only
        . simp_all [Sum.isRight_iff, BoundedFormula.relabelAux]
          by_cases h' : (g a).isLeft
          . simp_all [Sum.isLeft_iff]
            aesop
          . simp_all [Sum.isRight_iff]
            aesop
      · intro b
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        by_cases h' : (g a).isLeft
        . simp_all [Sum.isLeft_iff]
          simp_all [BoundedFormula.relabelAux]
          aesop
        . simp_all [Sum.isRight_iff, BoundedFormula.relabelAux]
          obtain ⟨w, h_2⟩ := h'
          simp_all
          induction n with
          | zero =>
            simp_all [Fin.cast, Fin.castAdd, Fin.castLE]
            exact Fin.elim0 w
          | succ n' ih =>
            simp_all [Fin.castAdd, Fin.natAdd, Fin.castLE]
            rw [@Nat.le_antisymm_iff] at a_1
            have ⟨a_1, hc⟩ := a_1
            simp only [← Nat.not_gt_eq] at hc
            apply hc
            simp_all only [true_and, gt_iff_lt, not_lt]
            apply Fin.val_lt_of_le w
            simp

    · intro b
      apply And.intro
      · intro a
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        by_cases h' : (g a).isLeft
        . simp_all [Sum.isLeft_iff]
          simp_all [BoundedFormula.relabelAux]
          aesop
        . simp_all [Sum.isRight_iff, BoundedFormula.relabelAux]
          obtain ⟨w, h_2⟩ := h'
          simp_all
          induction n with
          | zero =>
            simp_all [Fin.cast, Fin.castAdd, Fin.castLE]
            exact Fin.elim0 w
          | succ n' ih =>
            simp_all [Fin.castAdd, Fin.natAdd, Fin.castLE]
            rw [@Nat.le_antisymm_iff] at a_1
            have ⟨hc, a_1⟩ := a_1
            simp only [← Nat.not_gt_eq] at hc
            apply hc
            simp_all only [gt_iff_lt, not_lt]
            apply Fin.val_lt_of_le w
            simp
      · intro b_1 a
        simp_all [BoundedFormula.relabelAux]

/-- `(BoundedFormula.relabel g).schema` is equivalent to the partial image of `λ a => (g a).getLeft?`. -/
theorem BoundedQuery.relabel_schema {n k} {dbs : ρ → Finset String} (g : String → String ⊕ (Fin n)) (φ : BoundedQuery dbs k) :
  (φ.relabel g).schema = (φ.schema.pimage (λ a => (g a).getLeft?)) := by
    induction φ with
    | _ => aesop
