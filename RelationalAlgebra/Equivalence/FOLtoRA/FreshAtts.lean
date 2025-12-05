import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import Mathlib.Data.Finset.Fin

open RM

@[simp]
def toDot (n : ℕ) : String := n.fold (λ _ _ p ↦ p ++ ".") ""

@[simp]
theorem toDot.length (n : ℕ) : (toDot n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>  rw [toDot, Nat.fold_succ, String.length_append, ← toDot, ih, Nat.add_left_cancel_iff]; rfl

@[simp]
theorem toDot.length' (n m : ℕ) : (toDot n).length = m ↔ m = n := by
  induction m with
  | zero => rw [toDot.length (n := n)]; grind
  | succ n ih =>  rw [toDot.length]; grind

theorem toDot.inj : (toDot).Injective := by
  intro a₁ a₂ h
  let h' := toDot.length a₁
  rw [h, toDot.length' a₂ a₁] at h'
  exact h'


def freshStringsS (n : ℕ) : Set String := {a | ∃i ∈ (Finset.range n), toDot i = a}

instance freshStringsSFin : Fintype (freshStringsS n) := by
  apply Fintype.ofFinset (((Finset.range n).attachFin (by intro n h; simp at h; apply h)).image (toDot ∘ Fin.val))
  . simp
    intro s
    apply Iff.intro
    . intro ⟨a, ha⟩
      use a
      simp [ha]
    . intro ⟨a, ha, ha'⟩
      simp_all
      use ⟨a, ha⟩

def freshStrings (n : ℕ) : Finset String := (freshStringsS n).toFinset

theorem freshStringsS.range_def : Fintype.card (freshStringsS n) = (Finset.range n).card := by
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    rw [Finset.card_range] at *;
    nth_rewrite 3 [← ih]
    rw [@Fintype.card_ofFinset]
    rw [@Fintype.card_ofFinset]
    rw [@Finset.card_image_iff.mpr]
    . rw [@Finset.card_image_iff.mpr]
      . simp
      . exact Set.injOn_of_injective (Function.Injective.comp (toDot.inj) Fin.val_injective)
    . exact Set.injOn_of_injective (Function.Injective.comp (toDot.inj) Fin.val_injective)

theorem freshStrings.card_def : (freshStrings n).card = n := by
  rw [freshStrings, Set.toFinset_card, freshStringsS.range_def, Finset.card_range]

theorem freshStrings.excl {rs : Finset String} (h : x ∈ (freshStrings (rs.card + 1) \ rs)) : x ∉ rs := by
  simp_all only [Finset.mem_sdiff, not_false_eq_true]


open FOL Language BoundedFormula

@[simp]
def FreshAttsAux (rs : Finset String) (n : ℕ) : Finset String :=
  (freshStrings (n + rs.card)) \ rs

theorem FreshAttsAux.empty_inter : FreshAttsAux rs n ∩ rs = ∅ := by simp

@[simp]
theorem FreshAttsAux.card_def : ∃m, (FreshAttsAux rs n).card = n + m := by
  rw [FreshAttsAux, Finset.card_sdiff, freshStrings.card_def]
  rw [Nat.add_sub_assoc]
  . grind
  . rw [Finset.card_inter, tsub_le_iff_right, add_le_add_iff_left]
    exact Finset.card_le_card Finset.subset_union_right

@[simp]
def FreshAtts [Fintype ↑(adomAtts dbs (α := String))] (f : (fol dbs).BoundedFormula String n) : Finset String :=
  FreshAttsAux (f.freeVarFinset ∪ (adomAtts dbs).toFinset ∪ {default}) (n + 1 + depth f)

theorem FreshAtts.empty_inter_freeVarFinset [Fintype ↑(adomAtts dbs (α := String))] {f : (fol dbs).BoundedFormula String n} :
  FreshAtts f ∩ f.freeVarFinset = ∅ := by simp; grind

theorem FreshAtts.empty_inter_dbs [Fintype ↑(adomAtts dbs (α := String))] {f : (fol dbs).BoundedFormula String n} :
  FreshAtts f ∩ (adomAtts dbs).toFinset = ∅ := by simp; grind

theorem FreshAtts.empty_inter_union [Fintype ↑(adomAtts dbs (α := String))] {f : (fol dbs).BoundedFormula String n} :
  FreshAtts f ∩ (f.freeVarFinset ∪ (adomAtts dbs).toFinset ∪ {""}) = ∅ := by simp; grind

example (rs rs' : Finset String) : (rs ∩ rs').card ≤ rs.card := by
  rw [Finset.card_inter, tsub_le_iff_right, add_le_add_iff_left]
  exact Finset.card_le_card Finset.subset_union_right

@[simp]
theorem FreshAtts.card_def [Fintype ↑(adomAtts dbs (α := String))] (f : (fol dbs).BoundedFormula String n) : ∃m, (FreshAtts f).card = n + 1 + depth f + m := by
  rw [FreshAtts]
  exact FreshAttsAux.card_def


@[simp]
theorem FreshAtts.card_gt_def [Fintype ↑(adomAtts dbs (α := String))] {f : (fol dbs).BoundedFormula String n} : n + depth f < (FreshAtts f).card  := by
  have ⟨k, hk⟩ := FreshAtts.card_def (f := f)
  rw [hk]
  grind


theorem FreshString.get_proof : 0 < (RelationSchema.ordering (freshStrings (rs.card + 1) \ rs)).length := by
  rw [RelationSchema.ordering_card, Finset.card_pos]
  apply Finset.sdiff_nonempty_of_card_lt_card
  rw [freshStrings.card_def]
  exact lt_add_one rs.card

def FreshString (rs : Finset String) : String :=
  (RelationSchema.ordering (freshStrings (rs.card + 1) \ rs))[0]'FreshString.get_proof

theorem FreshString.notMem_rs : FreshString rs ∉ rs := by
  apply freshStrings.excl
  simp_rw [FreshString, ← RelationSchema.ordering_mem]
  exact List.getElem_mem get_proof
