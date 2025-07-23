import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Util
import RelationalAlgebra.Util.Equiv

import Mathlib.Data.Finset.Image
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Defs

open RM

-- Selection and Difference are 'trivial', hence they do not include proofs yet

def selectionT (inTuples : Set Tuple) (x : Attribute) (y : Attribute ⊕ Value) (positiveEq : Bool) : Set Tuple :=
  {t | t ∈ inTuples ∧ ite positiveEq (t x = Sum.elim t id y) (t x ≠ Sum.elim t id y)}

@[simp]
theorem selectionT.def_att (a : Attribute) (t : Tuple) : Sum.elim t id (Part.some <$> Sum.inl a) = t a := rfl

@[simp]
theorem selectionT.def_val (v : Value) (t : Tuple) : Sum.elim t id (Part.some <$> Sum.inr v) = .some v := rfl

theorem selectionDom {x y t} {not : Bool} {inst : RelationInstance} (h : t ∈ selectionT inst.tuples x y not) :
  PFun.Dom t = inst.schema := by
    simp_all only [selectionT, Part.coe_some, bind_pure_comp, Set.mem_setOf_eq]
    cases y
    all_goals exact inst.validSchema t h.1

def selection (inst : RelationInstance) (x : Attribute) (y : Attribute ⊕ Value) (not : Bool) : RelationInstance :=
⟨
  inst.schema,
  selectionT inst.tuples x y not,
  fun _ ht ↦ selectionDom ht
⟩

def diffT (inTuplesA inTuplesB : Set Tuple) : Set Tuple :=
  Set.diff inTuplesA inTuplesB

def diff (inst inst' : RelationInstance) : RelationInstance :=
⟨
  inst.schema,
  diffT inst.tuples inst'.tuples,
  by
    intro t a
    exact inst.validSchema t a.1
⟩

-- Union
section union

def unionT (inTuples inTuples' : Set Tuple) : Set Tuple :=
  inTuples ∪ inTuples'

def union (inst inst' : RelationInstance) (h: inst.schema = inst'.schema): RelationInstance := ⟨
    inst.schema,
    unionT inst.tuples inst'.tuples,
    λ v hv => Or.elim hv (λ hv_l => inst.validSchema v hv_l) (λ hv_r => Eq.trans (inst'.validSchema v hv_r) (by rw [h.symm]))
  ⟩

@[simp]
theorem union_empty (inst : RelationInstance) : union inst (∅r inst.schema) rfl = inst :=
  by simp_all only [union, unionT, Set.union_empty]

@[simp]
theorem union_comm (inst inst' : RelationInstance) (h : inst.schema = inst'.schema) : union inst inst' h = union inst' inst h.symm :=
  by simp only [union, unionT, h, Set.union_comm inst.tuples inst'.tuples]

@[simp]
theorem union_assoc (inst inst' inst'' : RelationInstance) (h : inst.schema = inst'.schema) (h' : inst'.schema = inst''.schema) :
  union (union inst inst' h) inst'' (h.trans h') = union inst (union inst' inst'' h') (by simp [union, h]) :=
    by simp only [union, unionT, Set.union_assoc inst.tuples inst'.tuples inst''.tuples]

end union


-- Rename
section rename

def renameSchema (schema : RelationSchema) (f : Attribute → Attribute) : RelationSchema := schema.image f

@[simp]
theorem rename_schema_id (schema : RelationSchema) : renameSchema schema id = schema := by
    unfold renameSchema
    simp_all only [Finset.image_id]

def renameT (inTuples : Set Tuple) (f : Attribute → Attribute) : Set Tuple :=
  { t' | ∃ t ∈ inTuples, t' ∘ f = t }

theorem renameDom {f t} (inst : RelationInstance) (f_bij : f.Bijective) (h : t ∈ renameT inst.tuples f):
  PFun.Dom t = renameSchema inst.schema f := by
    ext a
    simp_all only [renameSchema, exists_eq_right', Set.mem_setOf_eq, PFun.mem_dom, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, renameT]
    apply Iff.intro
    -- value in new tuple → attribute in new schema
    · intro ⟨w, w_ta⟩
      simp [← Finset.mem_coe]
      rw [← inst.validSchema (t ∘ f)]
      . simp_all only [PFun.mem_dom, Function.comp_apply]
        have ⟨a', ha'⟩ := f_bij.right a
        rw [← ha'] at w_ta ⊢
        exact Exists.intro a' (And.intro (Exists.intro w w_ta) rfl)
      . exact h
    -- attribute in new schema → value in new tuple
    · intro ⟨w, w_in_schema, fw_a⟩
      rw [← fw_a]
      simp [← Finset.mem_coe] at w_in_schema
      rw [← inst.validSchema (t ∘ f) h] at w_in_schema
      exact Part.dom_iff_mem.mp w_in_schema


def rename (inst : RelationInstance) (f : Attribute → Attribute) (f_sur : f.Bijective) : RelationInstance := ⟨
    renameSchema inst.schema f,
    renameT inst.tuples f,
    fun _ ht => renameDom inst f_sur ht
  ⟩

@[simp]
theorem rename_inst_id (inst : RelationInstance) : rename inst id Function.bijective_id = inst := by
  unfold rename
  simp_all only [rename_schema_id, Function.comp_id, exists_eq_right', Set.setOf_mem_eq, renameT]

@[simp]
theorem rename_comp (inst : RelationInstance) (f : Attribute → Attribute) (f_bij : f.Bijective) (g : Attribute → Attribute) (g_bij : g.Bijective) :
    rename (rename inst f f_bij) g g_bij = rename inst (g ∘ f) (Function.Bijective.comp g_bij f_bij) := by
      unfold rename renameSchema
      simp_all only [exists_eq_right', Set.mem_setOf_eq, RelationInstance.mk.injEq, renameT]
      apply And.intro
      · ext x : 1
        simp_all only [Finset.mem_image, exists_exists_and_eq_and, Function.comp_apply]
      · rfl

@[simp]
theorem rename_inv (inst : RelationInstance) (f : Attribute → Attribute) (f_bij : f.Bijective) (g : Attribute → Attribute) (g_bij : g.Bijective) (c : g ∘ f = id) :
  rename (rename inst f f_bij) g g_bij = inst := by simp_all only [rename_comp, rename_inst_id]

end rename


-- Join
section join

def joinT (inTuples1 inTuples2 : Set Tuple) : Set Tuple :=
  { t | ∃ t1 ∈ inTuples1, ∃ t2 ∈ inTuples2,
    (∀ a : Attribute, (a ∈ t1.Dom → t a = t1 a) ∧ (a ∈ t2.Dom → t a = t2 a) ∧ (a ∉ t1.Dom ∪ t2.Dom → t a = Part.none))
  }

def joinDom {t} (inst1 inst2 : RelationInstance) (h : t ∈ joinT inst1.tuples inst2.tuples):
  PFun.Dom t = inst1.schema ∪ inst2.schema := by
    simp_all only [Set.mem_setOf_eq, joinT]
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    ext a
    simp_all only [PFun.mem_dom]
    simp [← Finset.mem_coe]
    rw [← inst1.validSchema w left, ← inst2.validSchema w_1 left_1]
    simp_all only [PFun.mem_dom]
    apply Iff.intro
    · intro a_1
      obtain ⟨w_2, h⟩ := a_1
      by_cases g : a ∈ w.Dom ∪ w_1.Dom
      simp_all only [forall_exists_index, Set.mem_union, PFun.mem_dom, not_or, not_exists, and_imp]
      . simp_all only [not_false_eq_true, Part.not_mem_none]
    · intro a_1
      by_cases g : a ∈ inst1.schema ∪ inst2.schema
      . simp_all only [Finset.mem_union, not_or, and_imp]
        cases a_1
        all_goals (cases g; all_goals simp_all only)
      . simp [← Finset.mem_coe] at g
        rw [← inst1.validSchema w left, ← inst2.validSchema w_1 left_1] at g
        simp_all only [Finset.mem_union, not_or, and_imp, PFun.mem_dom, not_exists, exists_const, or_self]

def join (inst1 inst2 : RelationInstance) : RelationInstance :=
    ⟨
      inst1.schema ∪ inst2.schema,
      joinT inst1.tuples inst2.tuples,
      fun _ ht => joinDom inst1 inst2 ht
    ⟩

@[simp]
theorem join_comm (inst1 inst2 : RelationInstance) : join inst1 inst2 = join inst2 inst1 := by
  simp_all only [join, RelationInstance.mk.injEq, joinT]
  apply And.intro
  · ext t : 1
    apply Iff.intro
    all_goals
    · simp_all only [Finset.mem_union]
      intro h
      cases h
      all_goals simp_all only [or_true, true_or]
  · ext t : 1
    apply Iff.intro
    all_goals
    · intro a
      obtain ⟨t1, ht1, t2, ht2, h⟩ := a
      apply Exists.intro
      · apply And.intro
        · exact ht2
        · simp_all only [PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp]
          apply Exists.intro
          · apply And.intro ht1
            . intro a
              simp_all only [not_false_eq_true, implies_true, and_true]
              exact And.intro (h a).2.1 (h a).1

@[simp]
theorem join_empty (inst : RelationInstance) :
  join inst (∅r inst.schema)  = ∅r inst.schema := by
    simp_all only [join, Finset.union_idempotent, Set.mem_empty_iff_false, false_and, exists_const,
      and_false, Set.setOf_false, RelationInstance.empty, joinT]

@[simp]
theorem empty_join (inst : RelationInstance) :
  join (∅r inst.schema) inst = ∅r inst.schema := by simp_all only [join_comm, join_empty]

@[simp]
theorem join_self (inst : RelationInstance) : join inst inst = inst := by
  simp only [join, Finset.union_idempotent, ← RelationInstance.eq, true_and, joinT]
  ext t
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  . intro ⟨t1, ht1, t2, ht2, h1⟩
    have t_eq_t1 : t = t1 := by
      have t1_dom : t1.Dom = inst.schema := inst.validSchema t1 ht1
      have t2_dom : t2.Dom = inst.schema := inst.validSchema t2 ht2
      simp_all only [Set.union_self]
      ext a v
      by_cases hc : a ∈ inst.schema
      . simp_all only [Finset.mem_coe]
      . have z := (h1 a).2.2 hc
        simp_all only [not_false_eq_true, Part.not_mem_none, false_iff]
        by_contra hc2
        apply hc
        have z2 : a ∈ t1.Dom := by
          simp [PFun.mem_dom]
          apply Exists.intro v hc2
        rw [t1_dom] at z2
        simp_all only [Finset.mem_coe]
    simp_all only
  . intro h
    have g : ∀a : Attribute, (a ∉ t.Dom ∪ t.Dom → t a = Part.none) := by
        simp_all only [Set.union_self, PFun.mem_dom, not_exists]
        intro a a_1
        ext a_2 : 1
        simp_all only [Part.not_mem_none]
    exact Exists.intro t (And.intro h (Exists.intro t (And.intro h (λ a => And.intro (λ _ => rfl) (And.intro (λ _ => rfl) (λ h' => g a h'))))))

end join


-- Projection
section projection

def projectionT (inTuples : Set Tuple) (s' : RelationSchema) : Set Tuple :=
  { t' | ∃ t ∈ inTuples, (∀ a, (a ∈ s' → t' a = t a) ∧ (a ∉ s' → t' a = Part.none)) }

theorem projectionDom {s' t} (inst : RelationInstance) (h : t ∈ projectionT inst.tuples s') (h2 : s' ⊆ inst.schema) : PFun.Dom t = ↑s' := by
    ext a
    simp_all only [PFun.mem_dom, projectionT]
    simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    apply Iff.intro
    · intro a_1
      obtain ⟨w_1, h⟩ := a_1
      by_cases h : a ∈ s'
      . simp_all only [imp_self, not_true_eq_false, IsEmpty.forall_iff, and_self, Finset.mem_coe]
      . simp_all only [not_false_eq_true, Part.not_mem_none]
    · intro a_1
      have z : w.Dom = inst.schema := inst.validSchema w left
      have z2 : a ∈ inst.schema := h2 a_1
      have z3 : (w a).Dom ↔ a ∈ inst.schema := Iff.symm (Eq.to_iff (congrFun (id (Eq.symm z)) a))
      simp_all only [iff_true, Part.dom_iff_mem]

def projection (inst : RelationInstance) (s' : RelationSchema) (h : s' ⊆ inst.schema) :
  RelationInstance :=
  ⟨
    s',
    projectionT inst.tuples s',
    fun _ ht ↦ projectionDom inst ht h
  ⟩

abbrev emptyProjection (inst : RelationInstance) : RelationInstance := ⟨
  ∅,
  {t' | ∃t ∈ inst.tuples, t.restrict t.Dom.empty_subset = t'},
  by
    intro _ ⟨_, _, right⟩
    subst right
    simp only [Finset.coe_empty]
    rfl
⟩

-- This behavior is undefined in (most?) theory, so maybe should just leave it out
theorem projection_empty (inst : RelationInstance) : projection inst ∅ inst.schema.empty_subset = emptyProjection inst := by
      simp_all only [projection, RelationInstance.mk.injEq, true_and, projectionT]
      ext x : 1
      simp_all only [Finset.not_mem_empty, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and, exists_and_right]
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
    unfold projection projectionT
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
          simp_all only [← Finset.mem_coe, ← inst.validSchema w left, PFun.mem_dom,
            forall_exists_index, not_exists]
      rw [z] at left
      exact left
    · intro a
      apply Exists.intro t'
      simp_all only [implies_true, true_and]
      intro a_1 a_2
      simp [← Finset.mem_coe] at a_2
      rw [← inst.validSchema t' a] at a_2
      simp_all only [PFun.mem_dom, not_exists]
      ext a_3 : 1
      simp_all only [Part.not_mem_none]

theorem projection_cascade {s1 s2 : RelationSchema} (inst : RelationInstance) (h1 : s1 ⊆ inst.schema) (h2 : s2 ⊆ s1) :
  projection (projection inst s1 h1) s2 h2 = projection inst s2 (subset_trans h2 h1) := by
    simp [projection, projectionT]
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
      simp [← Finset.coe_subset] at h1
      rw [← inst.validSchema w left] at h1
      use PFun.restrict w h1
      apply And.intro
      · use w
        simp_all only [true_and]
        intro a
        apply And.intro
        · intro a_1
          ext a_2 : 1
          simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
        · intro a_1
          ext a_2 : 1
          simp_all only [PFun.mem_restrict, Finset.mem_coe, false_and, Part.not_mem_none]
      · intro a a_1
        ext a_2 : 1
        simp_all only [PFun.mem_restrict, iff_and_self]
        intro a_3
        apply h2
        simp_all only

end projection
