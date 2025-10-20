import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Util
import RelationalAlgebra.Util.Equiv

import Mathlib.Data.Finset.Image
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Defs

open RM

-- Selection and Difference are 'trivial', hence they do not include proofs yet

@[simp]
def selectionT (inTuples : Set Tuple) (x y : Attribute) : Set Tuple :=
  {t | t ∈ inTuples ∧ t x = t y}

theorem selectionDom {x y t} {inst : RelationInstance} (h : t ∈ selectionT inst.tuples x y) :
  PFun.Dom t = inst.schema := by
    simp_all only [selectionT, Part.coe_some, bind_pure_comp, Set.mem_setOf_eq]
    cases y
    all_goals exact inst.validSchema t h.1

def selection (inst : RelationInstance) (x y : Attribute) : RelationInstance :=
⟨
  inst.schema,
  selectionT inst.tuples x y,
  fun _ ht ↦ selectionDom ht
⟩

@[simp]
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

@[simp]
def unionT (inTuples inTuples' : Set Tuple) : Set Tuple :=
  inTuples ∪ inTuples'

def union (inst inst' : RelationInstance) (h: inst.schema = inst'.schema): RelationInstance := ⟨
  inst.schema,
  unionT inst.tuples inst'.tuples,
  λ v hv => Or.elim hv (λ hv_l => inst.validSchema v hv_l) (λ hv_r => Eq.trans (inst'.validSchema v hv_r) (by rw [h.symm]))
⟩

@[simp]
theorem unionT_empty (ts : Set Tuple) : unionT ts {} = ts :=
  by simp_all only [unionT, Set.union_empty]

@[simp]
theorem unionT_comm (ts ts' : Set Tuple) : unionT ts ts' = unionT ts' ts :=
  by simp only [unionT, Set.union_comm]

@[simp]
theorem unionT_assoc (ts ts' ts'' : Set Tuple) :
  unionT (unionT ts ts') ts'' = unionT ts (unionT ts' ts'' ) :=
    by simp [unionT, Set.union_assoc]

end union


-- Rename
section rename

@[simp]
def renameSchema (schema : RelationSchema) (f : Attribute → Attribute) : RelationSchema := schema.image f

@[simp]
theorem rename_schema_id (schema : RelationSchema) : renameSchema schema id = schema := by
    unfold renameSchema
    simp_all only [Finset.image_id]

@[simp]
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
theorem renameT_inst_id (ts : Set Tuple) : renameT ts id = ts := by
  simp_all only [renameT, Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem renameT_comp (ts : Set Tuple) (f : Attribute → Attribute) (g : Attribute → Attribute) :
    renameT (renameT ts f) g = renameT ts (g ∘ f) := by
      simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq]
      rfl

@[simp]
theorem renameT_inv (ts : Set Tuple) (f : Attribute → Attribute) (g : Attribute → Attribute) (c : g ∘ f = id) :
  renameT (renameT ts f) g = ts := by
    simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq, Function.comp_assoc,
      Function.comp_id, Set.setOf_mem_eq]

end rename


-- Join
section join

@[simp]
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
theorem joinT_comm (ts₁ ts₂ : Set Tuple) : joinT ts₁ ts₂ = joinT ts₂ ts₁ := by
  ext t
  simp_all only [joinT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists,
    and_imp, Set.mem_setOf_eq]
  apply Iff.intro
  all_goals (
    intro ⟨t₁, ht₁, t₂, ht₂, ht₃⟩
    use t₂
    apply And.intro ht₂
    use t₁
    apply And.intro ht₁
    intro a
    apply And.intro (ht₃ a).2.1
    apply And.intro (ht₃ a).1
    intro h' h''
    exact (ht₃ a).2.2 h'' h'
  )

@[simp]
theorem joinT_empty (ts : Set Tuple) :
  joinT ts {} = {} := by
    simp_all only [joinT, Set.mem_empty_iff_false, PFun.mem_dom, forall_exists_index, Set.mem_union,
      not_or, not_exists, and_imp, false_and, exists_const, and_false, Set.setOf_false]

@[simp]
theorem empty_joinT (ts : Set Tuple) :
  joinT {} ts = {} := by simp_all only [joinT_comm, joinT_empty]

@[simp]
theorem joinT_self (ts : Set Tuple) (h : ∀t ∈ ts, ∀t' ∈ ts, t.Dom = t'.Dom) : joinT ts ts = ts := by
  simp only [joinT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp]
  ext t
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  . intro ⟨t1, ht1, t2, ht2, h1⟩
    have t_eq_t1 : t = t1 := by
      have t1_dom : t1.Dom = t2.Dom := by simp_all [Set.ext_iff]; exact h t1 ht1 t2 ht2
      ext a v
      by_cases hc : a ∈ t1.Dom
      . simp at hc
        have ⟨v, hv⟩ := hc
        rw [(h1 a).1 v hv]
      . have hv : a ∉ t2.Dom := by simp_all
        simp at hc hv
        simp [(h1 a).2.2 hc hv, hc]
    simp_all only
  . intro h
    have g : ∀a : Attribute, (a ∉ t.Dom → t a = Part.none) := by
        simp_all only [Set.union_self, PFun.mem_dom, not_exists]
        intro a a_1
        ext a_2 : 1
        simp_all only [Part.not_mem_none]
    simp at g
    exact Exists.intro t (And.intro h (Exists.intro t (And.intro h (λ a => And.intro (λ _ => by simp) (And.intro (λ _ => by simp) (λ h' h'' => g a h'))))))

end join


-- Projection
section projection

@[simp]
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

theorem projectionT_empty (ts : Set Tuple) : projectionT ts ∅ = ts.image (λ _ => (λ _ => .none)) := by
  simp_all only [projectionT, Finset.not_mem_empty, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and,
    exists_and_right]
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_image, exists_and_right, and_congr_right_iff, forall_exists_index]
  intro x_1 h
  apply Iff.intro
  · intro a
    ext a_1 b : 1
    simp_all only [Part.not_mem_none]
  · intro a a_1
    subst a
    simp_all only

theorem projectionT_id {rs : RelationSchema} (ts : Set Tuple) (h : ∀t ∈ ts, rs = t.Dom) : projectionT ts rs = ts
  := by
    simp_all only [projectionT]
    ext t
    simp_all only [Set.mem_setOf_eq]
    apply Iff.intro
    · intro a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      convert left
      ext a v
      by_cases hc : a ∈ rs
      . simp_all only
      . simp_all only [not_false_eq_true, Part.not_mem_none, false_iff]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        simp_all only [← Finset.mem_coe, PFun.mem_dom,
          forall_exists_index, not_exists, h w left]
    · intro ht
      use t
      simp [ht]
      intro a ha
      simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, ← h t ht, ha]

theorem projectionT_cascade {s0 s1 s2 : RelationSchema} (ts : Set Tuple) (h0 : ∀t ∈ ts, s0 = t.Dom) (h1 : s1 ⊆ s0) (h2 : s2 ⊆ s1) :
  projectionT (projectionT ts s1) s2 = projectionT ts s2 := by
    simp [projectionT]
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
      simp [h0 w left] at h1
      use PFun.restrict w h1
      apply And.intro
      · apply Exists.intro
        · apply And.intro
          · exact left
          · intro a
            apply And.intro
            · intro a_1
              ext a_2 : 1
              simp_all only [PFun.mem_restrict, Finset.mem_coe, true_and]
            · intro a_1
              ext a_2 : 1
              simp_all only [PFun.mem_restrict, Finset.mem_coe, false_and, Part.not_mem_none]
      · intro a a_1
        ext a_2 : 1
        simp_all only [PFun.mem_restrict, Finset.mem_coe, iff_and_self]
        intro a_3
        apply h2
        simp_all only

end projection
