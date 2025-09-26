import RelationalAlgebra.FOL.WellTyped
import RelationalAlgebra.FOL.Relabel

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem relabel.Injective_def {k n : ℕ} {g : (Attribute ⊕ Fin k) → (Attribute ⊕ Fin n)} (h : g.Injective) :
  Function.Injective (Term.relabel g : fol.Term (Attribute ⊕ Fin k) → fol.Term (Attribute ⊕ Fin n)) := by
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

@[simp]
theorem relabel.Injective_relabelAux {k n : ℕ} {g : Attribute → (Attribute ⊕ Fin n)} (h : g.Injective) :
  Function.Injective (BoundedFormula.relabelAux g k) := by
    simp_all [Function.Injective]
    apply And.intro
    · intro a
      apply And.intro
      · intro a_1 a_2
        by_cases h' : (g a_1).isLeft
        . simp_all [Sum.isLeft_iff]
          nth_rewrite 2 [BoundedFormula.relabelAux] at a_2
          aesop
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
            simp_all [Fin.cast, Fin.castAdd, Fin.natAdd, Fin.castLE]
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
            simp_all [Fin.cast, Fin.castAdd, Fin.natAdd, Fin.castLE]
            rw [@Nat.le_antisymm_iff] at a_1
            have ⟨hc, a_1⟩ := a_1
            simp only [← Nat.not_gt_eq] at hc
            apply hc
            simp_all only [true_and, gt_iff_lt, not_lt]
            apply Fin.val_lt_of_le w
            simp
      · intro b_1 a
        simp_all [BoundedFormula.relabelAux]

theorem BoundedQuery.relabel_schema {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) :
  (φ.relabel g).schema = (φ.schema.pimage (λ a => (g a).getLeft?)) := by
    induction φ with
    | _ => aesop

@[simp]
theorem BoundedQuery.relabel_hasSafeTerm {n k} (g : Attribute → Attribute ⊕ (Fin n)) (φ : BoundedQuery k) (t : fol.Term (Attribute ⊕ Fin k)) (h : g.Injective):
  (φ.relabel g).hasSafeTerm (t.relabel (BoundedFormula.relabelAux g k)) = φ.hasSafeTerm t := by
    induction φ with
    | R dbs rn a =>
      rename_i k'
      simp [Relations.boundedFormula]
      have rel_inj : Function.Injective (Term.relabel (BoundedFormula.relabelAux g k')) := relabel.Injective_def (relabel.Injective_relabelAux h)
      cases k
      all_goals
        apply Iff.intro
        all_goals
        · intro ⟨w, h_1⟩
          use w
          try apply rel_inj
          simp_all only [Term.relabel]

    | ex q q_ih =>
      have z := (q_ih (Term.relabel (Sum.map id (Fin.castLE (by simp))) t))
      simp_all [z.symm]

    | _ => aesop

@[simp]
theorem BoundedQuery.relabel_isWellTyped {n k} (g : Attribute → Attribute ⊕ (Fin n)) (h : g.Injective) (φ : BoundedQuery k) (h : φ.isWellTyped dbs) :
  (φ.relabel g).isWellTyped dbs := by
    induction φ with
    | _ => simp_all

@[simp]
theorem BoundedQuery.relabel_isWellTyped_sumInl {n k} (g : Attribute → Attribute) (h : g.Injective) (φ : BoundedQuery k) :
  (φ.relabel ((Sum.inl ∘ g) : Attribute → Attribute ⊕ Fin n)).isWellTyped dbs → φ.isWellTyped dbs := by
    induction φ with
    | _ => simp_all [Sum.inl_injective]
