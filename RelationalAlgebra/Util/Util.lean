import RelationalAlgebra.RelationalModel

namespace RM

section empty

-- Utility to create empty RelationInstances
@[simp]
abbrev RelationInstance.empty (schema : RelationSchema) : RelationInstance := ⟨
  schema,
  ∅,
  by simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
⟩

prefix:100 "∅r " => RelationInstance.empty

end empty


section rename

-- Function for renaming a single attribute
def renameFunc [DecidableEq Attribute] (old new : Attribute) : Attribute → Attribute :=
  (λ a'' => if (a'' = new) then old else if (a'' = old) then new else a'')

-- Theorem proving that renameFunc is surjective
theorem rename_func_surjective [DecidableEq Attribute] (old new : Attribute) (h : old ≠ new) : (renameFunc old new).Surjective := by
  simp only [renameFunc, Function.Surjective]
  intro a''
  simp_all only [ne_eq]
  by_cases h_a' : a'' = new
  . subst h_a'
    apply Exists.intro
    · split
      on_goal 2 => {
        rename_i h_1
        simp_all only [ite_eq_left_iff, imp_false, Decidable.not_not]
        rfl
      }
      rename_i h_1
      subst h_1
      simp_all only [not_true_eq_false]
  . by_cases h_a : a'' = old
    . subst h_a
      simp_all only [not_false_eq_true, ite_eq_left_iff]
      apply Exists.intro
      · intro a
        split
        next h_1 =>
          simp_all only [not_false_eq_true]
          exact h_1
        next h_1 => simp_all only [not_true_eq_false]
    . apply Exists.intro
      · split
        rename_i h_3
        on_goal 2 => rename_i h_3
        on_goal 2 => split
        on_goal 2 => rename_i h_4
        on_goal 3 => {
          rename_i h_4
          rfl
        }
        subst h_3
        simp_all only [not_true_eq_false]
        subst h_4
        simp_all only [not_false_eq_true, not_true_eq_false]

-- Theorem proving that renameFunc is bijective
theorem rename_func_injective [DecidableEq Attribute] (old new : Attribute) (h : old ≠ new) : (renameFunc old new).Injective := by
  simp only [renameFunc, Function.Injective]
  intro a''
  simp_all only [ne_eq]
  by_cases h_a' : a'' = new
  . subst h_a'
    simp_all
    intro a' h
    split at h
    . simp_all only
    . split at h
      . simp_all only [not_true_eq_false]
      . simp_all only [not_false_eq_true, not_true_eq_false]
  . by_cases h_a : a'' = old
    . simp_all only [not_false_eq_true, ite_true, ite_false]
      intro a' h
      split at h
      -- -- . split at h
      . simp_all only [not_true_eq_false]
      . split at h
        . simp_all only
        . simp_all only [not_true_eq_false]
    . simp_all only [ite_false]
      intro a' h
      subst h
      simp_all only [ite_eq_left_iff, Classical.not_imp, ite_false, ite_eq_right_iff, imp_false,
        Decidable.not_not, not_false_eq_true, and_true, IsEmpty.forall_iff]

theorem rename_func_bijective [DecidableEq Attribute] (old new : Attribute) (h : old ≠ new) : (renameFunc old new).Bijective := by
  apply And.intro (rename_func_injective old new h) (rename_func_surjective old new h)

end rename
