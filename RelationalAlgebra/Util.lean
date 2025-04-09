import RelationalAlgebra.RelationalModel

open RM

section empty

@[simp]
def emptyInst {schema : RelationSchema} : RelationInstance := ⟨
  schema,
  ∅,
  by simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
⟩

end empty


section rename

def renameFunc [DecidableEq Attribute] (a a' : Attribute) : Attribute → Attribute :=
  (λ a'' => if (a'' = a') then a else if (a'' = a) then a' else a'')

theorem rename_func_surjective [DecidableEq Attribute] (a a' : Attribute) (h : a ≠ a') : (renameFunc a a').Surjective := by
  simp only [renameFunc, Function.Surjective]
  intro a''
  simp_all only [ne_eq]
  by_cases h_a' : a'' = a'
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
  . by_cases h_a : a'' = a
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

end rename
