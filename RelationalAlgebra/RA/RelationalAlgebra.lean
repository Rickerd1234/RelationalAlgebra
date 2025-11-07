import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Util
import RelationalAlgebra.Util.Equiv

import Mathlib.Data.Finset.Image
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Defs

open RM

section RA

variable {α μ : Type}

-- Selection and Difference are 'trivial', hence they do not include proofs yet

@[simp]
def selectionT (inTuples : Set (α →. μ)) (x y : α) : Set (α →. μ) :=
  {t | t ∈ inTuples ∧ t x = t y}

theorem selectionDom {x y t} {inst : RelationInstance α μ} (h : t ∈ selectionT inst.tuples x y) :
  PFun.Dom t = inst.schema := by
    simp_all only [selectionT, Set.mem_setOf_eq]
    all_goals exact inst.validSchema t h.1

def selection (inst : RelationInstance α μ) (x y : α) : RelationInstance α μ :=
⟨
  inst.schema,
  selectionT inst.tuples x y,
  fun _ ht ↦ selectionDom ht
⟩

@[simp]
def diffT (inTuplesA inTuplesB : Set (α →. μ)) : Set (α →. μ) :=
  Set.diff inTuplesA inTuplesB

def diff (inst inst' : RelationInstance α μ) : RelationInstance α μ :=
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
def unionT (inTuples inTuples' : Set (α →. μ)) : Set (α →. μ) :=
  inTuples ∪ inTuples'

def union (inst inst' : RelationInstance α μ) (h: inst.schema = inst'.schema): RelationInstance α μ := ⟨
  inst.schema,
  unionT inst.tuples inst'.tuples,
  λ v hv => Or.elim hv (λ hv_l => inst.validSchema v hv_l) (λ hv_r => Eq.trans (inst'.validSchema v hv_r) (by rw [h.symm]))
⟩

@[simp]
theorem unionT_empty (ts : Set (α →. μ)) : unionT ts {} = ts :=
  by simp_all only [unionT, Set.union_empty]

@[simp]
theorem unionT_comm (ts ts' : Set (α →. μ)) : unionT ts ts' = unionT ts' ts :=
  by simp only [unionT, Set.union_comm]

@[simp]
theorem unionT_assoc (ts ts' ts'' : Set (α →. μ)) :
  unionT (unionT ts ts') ts'' = unionT ts (unionT ts' ts'' ) :=
    by simp [unionT, Set.union_assoc]

end union


-- Rename
section rename

@[simp]
def renameSchema (schema : Finset α) (f : α → α) [DecidableEq α] : Finset α := schema.image f

@[simp]
theorem rename_schema_id (schema : Finset α) [DecidableEq α] : renameSchema schema id = schema := by
    unfold renameSchema
    simp_all only [Finset.image_id]

@[simp]
def renameT (inTuples : Set (α →. μ)) (f : α → α) : Set (α →. μ) :=
  { t' | ∃ t ∈ inTuples, t' ∘ f = t }

theorem renameDom {f t} (inst : RelationInstance α μ) (f_bij : f.Bijective) (h : t ∈ renameT inst.tuples f) [DecidableEq α]:
  PFun.Dom t = renameSchema inst.schema f := by
    ext a
    simp_all only [renameSchema, exists_eq_right', Set.mem_setOf_eq, PFun.mem_dom, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, renameT]
    apply Iff.intro
    -- value in new tuple → α in new schema
    · intro ⟨w, w_ta⟩
      simp [← Finset.mem_coe]
      rw [← inst.validSchema (t ∘ f)]
      . simp_all only [PFun.mem_dom, Function.comp_apply]
        have ⟨a', ha'⟩ := f_bij.right a
        rw [← ha'] at w_ta ⊢
        exact Exists.intro a' (And.intro (Exists.intro w w_ta) rfl)
      . exact h
    -- α in new schema → value in new tuple
    · intro ⟨w, w_in_schema, fw_a⟩
      rw [← fw_a]
      simp [← Finset.mem_coe] at w_in_schema
      rw [← inst.validSchema (t ∘ f) h] at w_in_schema
      exact Part.dom_iff_mem.mp w_in_schema


def rename (inst : RelationInstance α μ) (f : α → α) (f_sur : f.Bijective) [DecidableEq α] : RelationInstance α μ := ⟨
    renameSchema inst.schema f,
    renameT inst.tuples f,
    fun _ ht => renameDom inst f_sur ht
  ⟩

@[simp]
theorem renameT_inst_id (ts : Set (α →. μ)) : renameT ts id = ts := by
  simp_all only [renameT, Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem renameT_comp (ts : Set (α →. μ)) (f : α → α) (g : α → α) :
    renameT (renameT ts f) g = renameT ts (g ∘ f) := by
      simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq]
      rfl

@[simp]
theorem renameT_inv (ts : Set (α →. μ)) (f : α → α) (g : α → α) (c : g ∘ f = id) :
  renameT (renameT ts f) g = ts := by
    simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq, Function.comp_assoc,
      Function.comp_id, Set.setOf_mem_eq]

end rename


-- Join
section join

@[simp]
def joinSingleT (t t1 t2 : α →. μ) : Prop :=
  (∀ a : α, (a ∈ t1.Dom → t a = t1 a) ∧ (a ∈ t2.Dom → t a = t2 a) ∧ (a ∉ t1.Dom ∪ t2.Dom → t a = Part.none))

def joinDomSingleT {t t1 t2 : α →. μ} (h : joinSingleT t t1 t2) [DecidableEq α]:
  PFun.Dom t = t1.Dom ∪ t2.Dom := by
    rw [joinSingleT] at h
    ext a
    apply Iff.intro
    · intro a_1
      by_cases g : a ∈ t1.Dom ∪ t2.Dom
      . simp_all only [Set.mem_union, not_or, and_imp, PFun.mem_dom]
      . simp_all only [Set.mem_union, not_or, and_imp, PFun.mem_dom, or_self, not_false_eq_true,
        Part.notMem_none, exists_false]
    · intro a_1
      simp_all only [Set.mem_union, not_or, and_imp, PFun.mem_dom]
      cases a_1 with
      | inl h =>
        simp_all only [← PFun.mem_dom]
      | inr h_1 =>
        simp_all only [← PFun.mem_dom]

@[simp]
def joinT (inTuples1 inTuples2 : Set (α →. μ)) : Set (α →. μ) :=
  { t | ∃ t1 ∈ inTuples1, ∃ t2 ∈ inTuples2,
    joinSingleT t t1 t2
  }

def joinDomSet {t rs1 rs2} (tuples1 tuples2 : Set (α →. μ)) (h : t ∈ joinT tuples1 tuples2) (h1 : ∀t1 ∈ tuples1, t1.Dom = rs1) (h2 : ∀t2 ∈ tuples2, t2.Dom = rs2) [DecidableEq α]:
  PFun.Dom t = rs1 ∪ rs2 := by
    rw [joinT, Set.mem_setOf_eq] at h
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    rw [joinDomSingleT right]
    simp_all

def joinDom {t} (inst1 inst2 : RelationInstance α μ) (h : t ∈ joinT inst1.tuples inst2.tuples) [DecidableEq α]:
  PFun.Dom t = inst1.schema ∪ inst2.schema := by
    rw [joinDomSet inst1.tuples inst2.tuples h inst1.validSchema inst2.validSchema, Finset.coe_union]

def join (inst1 inst2 : RelationInstance α μ) [DecidableEq α] : RelationInstance α μ :=
    ⟨
      inst1.schema ∪ inst2.schema,
      joinT inst1.tuples inst2.tuples,
      fun _ ht => joinDom inst1 inst2 ht
    ⟩

@[simp]
theorem joinT_comm (ts₁ ts₂ : Set (α →. μ)) : joinT ts₁ ts₂ = joinT ts₂ ts₁ := by
  ext t
  simp_all only [joinT, joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists,
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
theorem joinT_empty (ts : Set (α →. μ)) :
  joinT ts {} = {} := by
    simp_all only [joinT, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

@[simp]
theorem empty_joinT (ts : Set (α →. μ)) :
  joinT {} ts = {} := by simp_all only [joinT_comm, joinT_empty]

@[simp]
theorem joinT_self (ts : Set (α →. μ)) (h : ∀t ∈ ts, ∀t' ∈ ts, t.Dom = t'.Dom) : joinT ts ts = ts := by
  simp only [joinT, joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp]
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
    have g : ∀a : α, (a ∉ t.Dom → t a = Part.none) := by
        simp_all only [PFun.mem_dom, not_exists]
        intro a a_1
        ext a_2 : 1
        simp_all only [Part.notMem_none]
    simp at g
    exact Exists.intro t (And.intro h (Exists.intro t (And.intro h (λ a => And.intro (λ _ => by simp) (And.intro (λ _ => by simp) (λ h' h'' => g a h'))))))

end join


-- Projection
section projection

@[simp]
def projectionT (inTuples : Set (α →. μ)) (s' : Finset α) : Set (α →. μ) :=
  { t' | ∃ t ∈ inTuples, (∀ a, (a ∈ s' → t' a = t a) ∧ (a ∉ s' → t' a = Part.none)) }

theorem projectionDom {s' t} (inst : RelationInstance α μ) (h : t ∈ projectionT inst.tuples s') (h2 : s' ⊆ inst.schema) : PFun.Dom t = ↑s' := by
    ext a
    simp_all only [PFun.mem_dom, projectionT]
    simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    apply Iff.intro
    · intro a_1
      obtain ⟨w_1, h⟩ := a_1
      by_cases h : a ∈ s'
      . simp_all only
      . simp_all only [not_false_eq_true, Part.notMem_none]
    · intro a_1
      have z : w.Dom = inst.schema := inst.validSchema w left
      have z2 : a ∈ inst.schema := h2 a_1
      have z3 : (w a).Dom ↔ a ∈ inst.schema := Iff.symm (Eq.to_iff (congrFun (id (Eq.symm z)) a))
      simp_all only [iff_true, Part.dom_iff_mem]

def projection (inst : RelationInstance α μ) (s' : Finset α) (h : s' ⊆ inst.schema) :
  RelationInstance α μ :=
  ⟨
    s',
    projectionT inst.tuples s',
    fun _ ht ↦ projectionDom inst ht h
  ⟩

abbrev emptyProjection (inst : RelationInstance α μ) : RelationInstance α μ := ⟨
  ∅,
  {t' | ∃t ∈ inst.tuples, t.restrict t.Dom.empty_subset = t'},
  by
    intro _ ⟨_, _, right⟩
    subst right
    simp only [Finset.coe_empty]
    rfl
⟩

theorem projectionT_empty (ts : Set (α →. μ)) : projectionT ts ∅ = ts.image (λ _ => (λ _ => .none)) := by
  simp_all only [projectionT, Finset.notMem_empty, IsEmpty.forall_iff, not_false_eq_true,
    forall_const, true_and, exists_and_right]
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_image, exists_and_right, and_congr_right_iff, forall_exists_index]
  intro x_1 h
  apply Iff.intro
  · intro a
    ext a_1 b : 1
    simp_all only [Part.notMem_none]
  · intro a a_1
    subst a
    simp_all only

theorem projectionT_id {rs : Finset α} (ts : Set (α →. μ)) (h : ∀t ∈ ts, rs = t.Dom) : projectionT ts rs = ts
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
      . simp_all only [not_false_eq_true, Part.notMem_none, false_iff]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        simp_all only [← Finset.mem_coe, PFun.mem_dom,
          forall_exists_index, not_exists, h w left]
    · intro ht
      use t
      simp [ht]
      intro a ha
      simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, ← h t ht, ha]

theorem projectionT_cascade {s0 s1 s2 : Finset α} (ts : Set (α →. μ)) (h0 : ∀t ∈ ts, s0 = t.Dom) (h1 : s1 ⊆ s0) (h2 : s2 ⊆ s1) :
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
              simp_all only [PFun.mem_restrict, Finset.mem_coe, false_and, Part.notMem_none]
      · intro a a_1
        ext a_2 : 1
        simp_all only [PFun.mem_restrict, Finset.mem_coe, iff_and_self]
        intro a_3
        apply h2
        simp_all only

end projection
