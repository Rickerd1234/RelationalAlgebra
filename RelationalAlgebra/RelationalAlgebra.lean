import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Equiv
import RelationalAlgebra.Util
import Mathlib.Data.PFun
import Mathlib.Data.Part
import Mathlib.Logic.Function.Defs

open RM

-- Selection and Difference are 'trivial', hence they are not included yet


-- Union
section union

def union (inst inst' : RelationInstance) (h: inst.schema = inst'.schema): RelationInstance := ⟨
    inst.schema,
    inst.tuples ∪ inst'.tuples,
    λ v hv => Or.elim hv (λ hv_l => inst.validSchema v hv_l) (λ hv_r => Eq.trans (inst'.validSchema v hv_r) h.symm)
  ⟩

@[simp]
theorem union_empty (inst : RelationInstance) : union inst (∅r inst.schema) rfl = inst :=
  by unfold union; simp_all only [RelationInstance.empty, Set.union_empty]

@[simp]
theorem union_comm (inst inst' : RelationInstance) (h : inst.schema = inst'.schema) : union inst inst' h = union inst' inst h.symm :=
  by unfold union; simp [Set.union_comm inst.tuples inst'.tuples, h]

@[simp]
theorem union_assoc (inst inst' inst'' : RelationInstance) (h : inst.schema = inst'.schema) (h' : inst'.schema = inst''.schema) :
  union (union inst inst' h) inst'' (h.trans h') = union inst (union inst' inst'' h') (by simp [union, h]) :=
    by unfold union; simp [Set.union_assoc inst.tuples inst'.tuples inst''.tuples]

end union


-- Rename
section rename

def renameSchema (schema : RelationSchema) (f : Attribute → Attribute) : RelationSchema := schema.image f

@[simp]
theorem rename_schema_id (schema : RelationSchema) : renameSchema schema id = schema := by
    unfold renameSchema
    simp_all only [id_eq, Set.image_id']

def rename (inst : RelationInstance) (f : Attribute → Attribute) (f_sur : f.Surjective) : RelationInstance := ⟨
    renameSchema inst.schema f,
    { t' | ∃ t ∈ inst.tuples, t' ∘ f = t },
    by
      unfold renameSchema
      intro t' t_cond'
      simp_all only [exists_eq_right', Set.mem_setOf_eq]
      ext a
      simp_all only [PFun.mem_dom, Set.mem_image]
      apply Iff.intro
      -- value in new tuple → attribute in new schema
      · intro ⟨w, w_ta⟩
        rw [← inst.validSchema (t' ∘ f)]
        . simp_all only [PFun.mem_dom, Function.comp_apply]
          have ⟨a', ha'⟩ := f_sur a
          rw [← ha'] at w_ta ⊢
          exact Exists.intro a' (And.intro (Exists.intro w w_ta) rfl)
        . exact t_cond'
      -- attribute in new schema → value in new tuple
      · intro ⟨w, w_in_schema, fw_a⟩
        rw [← fw_a]
        rw [← inst.validSchema (t' ∘ f) t_cond'] at w_in_schema
        exact Part.dom_iff_mem.mp w_in_schema
  ⟩

@[simp]
theorem rename_inst_id (inst : RelationInstance) : rename inst id Function.surjective_id = inst := by
  unfold rename
  simp_all only [rename_schema_id, Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem rename_comp (inst : RelationInstance) (f : Attribute → Attribute) (f_sur : f.Surjective) (g : Attribute → Attribute) (b_sur : g.Surjective) :
    rename (rename inst f f_sur) g b_sur = rename inst (g ∘ f) (Function.Surjective.comp b_sur f_sur) := by
      unfold rename renameSchema
      simp_all only [exists_eq_right', Set.mem_setOf_eq, Function.comp_apply, RelationInstance.mk.injEq]
      apply And.intro
      · ext x : 1
        simp_all only [Set.mem_image, exists_exists_and_eq_and]
      · rfl

@[simp]
theorem rename_inv (inst : RelationInstance) (f : Attribute → Attribute) (f_sur : f.Surjective) (g : Attribute → Attribute) (g_sur : g.Surjective) (c : g ∘ f = id) :
  rename (rename inst f f_sur) g g_sur = inst := by simp_all only [rename_comp, rename_inst_id]

end rename


-- Join
section join

def join (inst1 : RelationInstance) (inst2 : RelationInstance) : RelationInstance :=
    ⟨
      inst1.schema ∪ inst2.schema,
      { t | ∃ t1 ∈ inst1.tuples, ∃ t2 ∈ inst2.tuples,
        (∀ a : Attribute, (a ∈ inst1.schema → t a = t1 a) ∧ (a ∈ inst2.schema → t a = t2 a) ∧ (a ∉ inst1.schema ∪ inst2.schema → t a = Part.none))
      },
      by
        intro t a
        simp_all only [and_imp, Set.mem_setOf_eq]
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := right
        obtain ⟨left_1, right⟩ := h
        ext a
        simp_all only [PFun.mem_dom, Set.mem_union]
        rw [← inst1.validSchema w left, ← inst2.validSchema w_1 left_1]
        simp_all only [not_or, and_imp, PFun.mem_dom]
        apply Iff.intro
        · intro a_1
          obtain ⟨w_2, h⟩ := a_1
          by_cases g : a ∈ inst1.schema ∪ inst2.schema
          . simp_all only [Set.mem_union]
            cases g with
            | inl h_1 =>
              simp_all only
              apply Or.inl
              apply Exists.intro
              · exact h
            | inr h_2 =>
              simp_all only
              apply Or.inr
              apply Exists.intro
              · exact h
          . simp_all only [Set.mem_union, not_or, not_false_eq_true, Part.not_mem_none]
        · intro a_1
          by_cases g : a ∈ inst1.schema ∪ inst2.schema
          . simp_all only [Set.mem_union]
            cases a_1 with
            | inl h =>
              cases g with
              | inl h_1 => simp_all only
              | inr h_2 =>
                simp_all only
                obtain ⟨w_2, h⟩ := h
                rw [← inst2.validSchema w_1 left_1] at h_2
                simp_all only [PFun.mem_dom]
            | inr h_1 =>
              cases g with
              | inl h =>
                simp_all only
                obtain ⟨w_2, h_1⟩ := h_1
                rw [← inst1.validSchema w left] at h
                simp_all only [PFun.mem_dom]
              | inr h_2 => simp_all only
          . rw [← inst1.validSchema w left, ← inst2.validSchema w_1 left_1] at g
            simp_all only [Set.mem_union, PFun.mem_dom, not_true_eq_false]
    ⟩

@[simp]
theorem join_comm (inst1 inst2 : RelationInstance) : join inst1 inst2 = join inst2 inst1 := by
  simp_all only [join, Set.mem_union, not_or, and_imp, RelationInstance.mk.injEq]
  apply And.intro
  · ext x : 1
    simp_all only [Set.mem_union]
    apply Iff.intro
    · intro a
      cases a with
      | inl h => simp_all only [or_true]
      | inr h_1 => simp_all only [true_or]
    · intro a
      cases a with
      | inl h => simp_all only [or_true]
      | inr h_1 => simp_all only [true_or]
  · ext x : 1
    simp_all only [Set.mem_setOf_eq]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      simp_all only [not_false_eq_true, implies_true, and_true]
      apply Exists.intro
      · apply And.intro
        · exact left_1
        · simp_all only [implies_true, true_and]
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {
              intro a a_1
              rfl
            }
            · simp_all only
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      simp_all only [not_false_eq_true, implies_true, and_true]
      apply Exists.intro
      · apply And.intro
        · exact left_1
        · simp_all only [implies_true, true_and]
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {
              intro a a_1
              rfl
            }
            · simp_all only

@[simp]
theorem join_empty (inst : RelationInstance) :
  join inst (∅r inst.schema)  = ∅r inst.schema := by
    simp_all only [RelationInstance.empty, join, Set.union_self, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

@[simp]
theorem empty_join (inst : RelationInstance) :
  join (∅r inst.schema) inst = ∅r inst.schema := by simp_all only [join_comm, join_empty]

@[simp]
theorem join_self (inst : RelationInstance) : join inst inst = inst := by
    simp only [join, Set.union_self, ← RelationInstance.eq, true_and]
    ext t
    simp only [Set.mem_setOf_eq]
    apply Iff.intro
    . intro ⟨ht1, ht2, _, _, ht5⟩
      have h : t = ht1 := by
        ext a v
        by_cases h : a ∈ inst.schema
        . simp_all only
        . simp_all only [not_false_eq_true, Part.not_mem_none, false_iff]
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          simp_all only [← inst.validSchema ht1 ht2, PFun.mem_dom, forall_exists_index, not_exists]
      rw [h]
      exact ht2
    . intro h
      have g : ∀a : Attribute, (a ∉ inst.schema → t a = Part.none) := by
          simp_all [← inst.validSchema t h]
          intro a a_1
          ext a_2 : 1
          simp_all only [Part.not_mem_none]
      exact Exists.intro t (And.intro h (Exists.intro t (And.intro h (λ a => And.intro (λ _ => rfl) (And.intro (λ _ => rfl) (λ h' => g a h'))))))

end join


-- Projection
section projection

def projection (inst : RelationInstance) (s' : RelationSchema) (h : s' ⊆ inst.schema) :
  RelationInstance :=
  ⟨
    s',
    { t' | ∃ t ∈ inst.tuples, (∀ a, (a ∈ s' → t' a = t a) ∧ (a ∉ s' → t' a = Part.none)) },
    by
      intro t' ⟨t, t_in_tuples, t_def'⟩
      ext a
      simp_all only [PFun.mem_dom]
      apply Iff.intro
      · intro ⟨w, w_ta'⟩
        have z := t_def' a
        by_cases h : a ∈ s'
        . simp_all only [imp_self, not_true_eq_false, IsEmpty.forall_iff, and_self]
        . simp_all only [not_false_eq_true, Part.not_mem_none]
      · intro a_1
        rw [← inst.validSchema t t_in_tuples] at h
        have z := Set.mem_of_subset_of_mem h a_1
        simp_all only [PFun.mem_dom]
  ⟩

abbrev emptyProjection (inst : RelationInstance) : RelationInstance := ⟨
  ∅,
  {t' | ∃t ∈ inst.tuples, t.restrict t.Dom.empty_subset = t'},
  by
    intro _ ⟨_, _, right⟩
    subst right
    exact rfl
⟩

-- This behavior is undefined in (most?) theory, so maybe should just leave it out
theorem projection_empty (inst : RelationInstance) : projection inst ∅ inst.schema.empty_subset = emptyProjection inst := by
      simp_all only [projection, Set.mem_empty_iff_false, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and,
        exists_and_right, RelationInstance.mk.injEq]
      ext x : 1
      simp_all only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w, h⟩ := left
        apply Exists.intro
        · apply And.intro
          · exact h
          · ext a b : 1
            simp_all only [PFun.mem_restrict, Set.mem_empty_iff_false, false_and, Part.not_mem_none]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        subst right
        apply And.intro
        · apply Exists.intro
          · exact left
        · intro a
          ext a_1 : 1
          simp_all only [PFun.mem_restrict, Set.mem_empty_iff_false, false_and, Part.not_mem_none]

theorem projection_id {s' : RelationSchema} (inst : RelationInstance) (h : s' = inst.schema) : projection inst s' (by subst h; simp_all only [subset_refl]) = inst
  := by
    unfold projection
    apply RelationInstance.eq.mp
    subst h
    simp_all only [true_and]
    ext t'
    simp_all only [Set.mem_setOf_eq]
    apply Iff.intro
    · intro ⟨w, left, right⟩
      have z : w = t' := by
        ext a v
        by_cases h : a ∈ inst.schema
        . simp_all only
        . simp_all only [not_false_eq_true, Part.not_mem_none, iff_false]
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          simp_all [← inst.validSchema w left]
      rw [z] at left
      exact left
    · intro a
      apply Exists.intro t'
      simp_all only [implies_true, true_and]
      intro a_1 a_2
      rw [← inst.validSchema t' a] at a_2
      simp_all only [PFun.mem_dom, not_exists]
      ext a_3 : 1
      simp_all only [Part.not_mem_none]

theorem projection_cascade {s1 s2 : RelationSchema} (inst : RelationInstance) (h1 : s1 ⊆ inst.schema) (h2 : s2 ⊆ s1) :
  projection (projection inst s1 h1) s2 h2 = projection inst s2 (subset_trans h2 h1) := by
    simp [projection]
    ext t'
    simp_all only [Set.mem_setOf_eq]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := left
      obtain ⟨left, right_1⟩ := h
      simp_all only [not_false_eq_true, implies_true, and_true]
      use w_1
      simp_all only [true_and]
      intro a a_1
      exact (right_1 a).1 (Set.mem_of_subset_of_mem h2 a_1)
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      simp_all only [not_false_eq_true, implies_true, and_true]
      rw [← inst.validSchema w left] at h1
      use PFun.restrict w h1
      apply And.intro
      · use w
        simp_all only [true_and]
        intro a
        apply And.intro
        · intro a_1
          ext a_2 : 1
          simp_all only [PFun.mem_restrict, true_and]
        · intro a_1
          ext a_2 : 1
          simp_all only [PFun.mem_restrict, false_and, Part.not_mem_none]
      · intro a a_1
        ext a_2 : 1
        simp_all only [PFun.mem_restrict, iff_and_self]
        intro a_3
        apply h2
        simp_all only

end projection
