import RelationalAlgebra.FOL.Realize

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem Term.realizeSome.tuple_restrict {dbi} [folStruc dbi] (t : fol.Term (Attribute ⊕ (Fin n))) {tup tup' : Tuple} {iv : Fin n →. Value} :
  Term.realizeSome dbi t tup' iv → (h_sub : tup'.Dom ⊆ tup.Dom) → tup' = tup.restrict h_sub → Term.realizeSome dbi t tup iv := by
    intro h_realize h_sub h_eq
    simp_all only [«def»]
    have ⟨t, ht⟩ := Term.cases t
    subst ht
    cases t with
    | inl a => exact h_sub h_realize
    | inr k => simp_all only [realize_var, Sum.elim_inr]

theorem Term.realizeSome.tuple_restrict2 {dbi} [folStruc dbi] (t : fol.Term (Attribute ⊕ (Fin n))) {tup : Tuple} {iv : Fin n →. Value} :
  Term.realizeSome dbi t tup iv → (h : ↑t.varFinsetLeft ⊆ tup.Dom) → tup' = tup.restrict h → Term.realizeSome dbi t tup' iv := by
    intro a h ht
    simp_all only [«def»]
    have ⟨t, ht⟩ := Term.cases t
    subst ht
    cases t with
    | inl a => simp [PFun.restrict, Part.restrict]
    | inr k => simp_all only [realize_var, Sum.elim_inr, varFinsetLeft.eq_2, implies_true]


@[simp]
theorem Relmap.tuple_restrict [folStruc : folStruc dbi] {t t' : Tuple} {tMap : Fin (dbi.schema rn).card → fol.Term (Attribute ⊕ (Fin n))}:
  folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim t' iv) (tMap i)) →
  (h : t'.Dom ⊆ t.Dom) → t' = t.restrict h →
    folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim t iv) (tMap i)) := by
      intro ht h ht'
      have z : (ArityToTuple fun i ↦ realize (Sum.elim (t.restrict h) iv) (tMap i)) = (ArityToTuple fun i ↦ realize (Sum.elim t iv) (tMap i)) := by
        ext a v
        apply Iff.intro
        · intro a_1
          unfold ArityToTuple at *
          simp_all only [PFun.dom_mk, DatabaseInstance.validSchema_def]
          split
          next h_1 =>
            simp_all only [↓reduceDIte, Part.dom_iff_mem]
            have ⟨k, hk⟩ := Term.cases (tMap (RelationSchema.index h_1))
            rw [hk]
            simp_all only [realize_var]
            cases k with
            | inl val => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe]
            | inr val_1 => simp_all only [Sum.elim_inr]
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]
        · intro a_1
          unfold ArityToTuple at *
          simp_all only [PFun.dom_mk, DatabaseInstance.validSchema_def]
          split
          next h_1 =>
            simp_all only [↓reduceDIte]
            have ⟨k, hk⟩ := Term.cases (tMap (RelationSchema.index h_1))
            have z := Term.RealizeSome.fromRelMap (RelationSchema.index h_1) ht
            rw [hk]
            simp_all only [realize_var]
            cases k with
            | inl val =>
              simp [Part.dom_iff_mem] at z a_1
              simp [a_1, z]
            | inr val_1 => simp_all only [Sum.elim_inr]
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]
      simp_all only [folStruc_apply_RelMap]


@[simp]
theorem Relmap.tuple_restrict2 [folStruc : folStruc dbi] {t : Tuple} (h : ↑((BoundedQuery.R rn tMap).schema) ⊆ t.Dom) :
  folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim t iv) (tMap i)) →
    folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim (PFun.restrict t h) iv) (tMap i)) := by
      intro ht
      have z : (ArityToTuple fun i ↦ realize (Sum.elim (t.restrict h) iv) (tMap i)) = (ArityToTuple fun i ↦ realize (Sum.elim t iv) (tMap i)) := by
        ext a v
        apply Iff.intro
        · intro a_1
          unfold ArityToTuple at *
          simp_all only [PFun.dom_mk, DatabaseInstance.validSchema_def]
          split
          next h_1 =>
            simp_all only [↓reduceDIte, Part.dom_iff_mem]
            have ⟨k, hk⟩ := Term.cases (tMap (RelationSchema.index h_1))
            rw [hk]
            simp_all only [realize_var]
            cases k with
            | inl val => simp_all only [Sum.elim_inl, PFun.mem_restrict, Finset.mem_coe]
            | inr val_1 => simp_all only [Sum.elim_inr]
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]
        · intro a_1
          simp_all
          have arityDom := RelationInstance.validSchema.def ht
          unfold ArityToTuple at *
          simp_all only [PFun.dom_mk, DatabaseInstance.validSchema_def]
          split
          next h_1 =>
            simp_all only [↓reduceDIte]
            have ⟨k, hk⟩ := Term.cases (tMap (RelationSchema.index h_1))
            rw [hk]
            simp_all only [realize_var]
            cases k with
            | inl
              val =>
              simp_all only [Sum.elim_inl, PFun.mem_restrict, BoundedQuery.schema.R_def, Set.coe_toFinset,
                Set.mem_setOf_eq, and_true]
              simp_all only [BoundedQuery.schema.R_def, Set.coe_toFinset]
              use RelationSchema.index h_1
              unfold varFinsetLeft
              split
              . simp_all only [var.injEq, Sum.inl.injEq, Finset.mem_singleton]
              . simp_all only [var.injEq, reduceCtorEq]
              . simp_all [emptyStructure]
            | inr val_1 => simp_all only [Sum.elim_inr]
          next h_1 => simp_all only [↓reduceDIte, Part.not_mem_none]
      simp_all only [folStruc_apply_RelMap]


@[simp]
theorem BoundedQuery.Realize.tuple_restrict [folStruc dbi] {n : ℕ} {q : BoundedQuery dbi.schema n} {t : Tuple} {iv : Fin n →. Value} (h_wt : q.isWellTyped)
  : q.Realize dbi t' iv → (h : t'.Dom ⊆ t.Dom) → t' = t.restrict h → q.Realize dbi t iv := by
    intro a h a_1
    induction q with
    | R rn tMap =>
      simp_all only [realizeSome.def, toFormula_rel, BoundedFormula.realize_rel]
      simp_all
      exact Relmap.tuple_restrict a h rfl

    | tEq sq t₁ t₂ ih  =>
      simp_all only [«def», isWellTyped.tEq_def, toFormula_tEq, BoundedFormula.realize_inf,
        true_and, forall_const, implies_true]
      obtain ⟨left, right⟩ := a

      have hDom₁ := Realize.all_terms h_wt.1 left t₁ h_wt.2.1
      have hDom₂ := Realize.all_terms h_wt.1 left t₂ h_wt.2.2

      · simp_all [BoundedFormula.Realize]
        obtain ⟨left_1, right_1⟩ := h_wt
        obtain ⟨left_3, right_1⟩ := right_1
        have ⟨t₁, ht₁⟩ := Term.cases t₁
        have ⟨t₂, ht₂⟩ := Term.cases t₂
        simp_all [ht₁, ht₂]
        cases t₁ with
        | inl att₁ =>
          simp_all
          cases t₂ with
          | inl att₂ =>
            by_cases hd₁ : (t' att₁).Dom
            . by_cases hd₂ : (t' att₂).Dom
              . simp [Part.ext_iff] at right ⊢
                simp [Part.dom_iff_mem] at hd₁ hd₂
                intro v
                apply Iff.intro
                . intro hv
                  exact ((right v).mp (And.intro hd₁ hv)).2
                . intro hv
                  exact ((right v).mpr (And.intro hd₂ hv)).2
              . simp_all
            . simp_all
          | inr fin₂ =>
            by_cases (t' att₁).Dom
            . simp_all
              rw [← right]
              ext v
              simp [PFun.mem_restrict]
              intro a
              subst ht₁ ht₂
              simp_all only
              exact Part.dom_iff_mem.mp hDom₂
            . simp_all
        | inr fin₁ =>
          cases t₂ with
          | inl att₂ =>
            by_cases (t' att₂).Dom
            . simp_all
              ext v
              simp [PFun.mem_restrict]
              intro a
              subst ht₁ ht₂
              simp_all only
              exact Part.dom_iff_mem.mp hDom₂
            . simp_all
          | inr fin₂ =>
            simp_all

    | ex q ih =>
      simp [BoundedQuery.Realize.def] at a ⊢ h_wt
      have ⟨w, hw⟩ := a
      use w
      simp_all only [«def», forall_const]

    | or q₁ q₂ ih₁ ih₂ =>
      simp [BoundedQuery.Realize.def] at ⊢ ih₁ ih₂ h_wt a
      simp_all only [forall_const]
      obtain ⟨left, right⟩ := h_wt
      obtain ⟨left_1, right⟩ := right
      cases a with
      | inl h_1 => simp_all only [true_or]
      | inr h_2 => simp_all only [or_true]

    | not q ih => simp_all [BoundedQuery.Realize.def]; sorry

    | _ => simp_all [BoundedQuery.Realize.def]

@[simp]
theorem BoundedQuery.Realize.tuple_restrict2 [folStruc dbi] {n : ℕ} {q : BoundedQuery dbi.schema n} {t : Tuple} {iv : Fin n →. Value} (h_wt : q.isWellTyped)
  : (h : ↑q.schema ⊆ t.Dom) → q.Realize dbi t iv → q.Realize dbi (t.restrict h) iv := by
    intro h h_rel
    induction q with
    | R rn tMap =>
      simp_all only [isWellTyped.R_def, toFormula_rel, BoundedFormula.realize_rel]
      simp_all [Relmap.tuple_restrict2 h h_rel,BoundedQuery.Realize.def]


    | tEq sq t₁ t₂ ih  =>
      simp only [«def», isWellTyped.tEq_def, toFormula_tEq, BoundedFormula.realize_inf,
        true_and, forall_const, implies_true, BoundedQuery.Realize.def] at h_rel h_wt ⊢
      simp_all
      obtain ⟨left, right⟩ := h_rel

      have hDom₁ := Realize.all_terms h_wt.1 left t₁ h_wt.2.1
      have hDom₂ := Realize.all_terms h_wt.1 left t₂ h_wt.2.2

      have ⟨t₁, ht₁⟩ := Term.cases t₁
      subst ht₁
      have ⟨t₂, ht₂⟩ := Term.cases t₂
      subst ht₂

      simp_all only [«def», realize_var, true_and]
      obtain ⟨left_1, right_1⟩ := h_wt
      obtain ⟨left_2, right_1⟩ := right_1
      cases t₁ with
      | inl val =>
        cases t₂ with
        | inl val_1 =>
          simp_all only [Sum.elim_inl, hasSafeTerm_mem_schema]
          ext a : 1
          simp_all only [Part.dom_iff_mem, BoundedFormula.Realize, realize_var, Sum.elim_inl,
            schema, PFun.mem_restrict, Finset.mem_coe, true_and]
        | inr val_2 =>
          simp_all only [Sum.elim_inl, hasSafeTerm_mem_schema, Sum.elim_inr]
          simp_all only [BoundedFormula.Realize, realize_var, Sum.elim_inl, Sum.elim_inr]
          ext a : 1
          simp_all only [PFun.mem_restrict, schema.tEq_def, Finset.mem_coe, true_and]
      | inr val_1 =>
        cases t₂ with
        | inl val =>
          simp_all only [Sum.elim_inr, Sum.elim_inl, hasSafeTerm_mem_schema]
          ext a : 1
          simp_all only [Part.dom_iff_mem, BoundedFormula.Realize, realize_var, Sum.elim_inr,
            Sum.elim_inl, schema, PFun.mem_restrict, Finset.mem_coe, true_and]
        | inr val_2 =>
          simp_all only [Sum.elim_inr]
          exact right

    | and q₁ q₂ ih₁ ih₂ =>
      simp only [«def», isWellTyped.and_def, toFormula_and, BoundedFormula.realize_inf,
        forall_const, implies_true] at h_rel h_wt ⊢
      simp_all
      obtain ⟨left, right⟩ := h_wt
      obtain ⟨left_1, right_1⟩ := h_rel
      apply And.intro
      · have h': ↑q₁.schema ⊆ t.Dom := by simp_all
        have := ih₁ h' left_1
        have h'' : ↑q₁.schema ⊆ ↑(q₁.and q₂).schema := by simp
        exact tuple_restrict left (ih₁ h' left_1) h'' rfl
      · have h': ↑q₂.schema ⊆ t.Dom := by simp_all
        have := ih₂ h' right_1
        have h'' : ↑q₂.schema ⊆ ↑(q₁.and q₂).schema := by simp
        exact tuple_restrict right (ih₂ h' right_1) h'' rfl

    | ex q ih =>
      simp only [«def», toFormula_ex, BoundedFormula.realize_ex, Nat.succ_eq_add_one,
        isWellTyped.ex_def] at h_rel h_wt ⊢
      simp_all only [«def», forall_const]
      obtain ⟨w, h_1⟩ := h_rel
      apply Exists.intro
      · apply @ih
        simp_all only [schema.ex_def, forall_true_left]
        apply h_1

    | or q₁ q₂ ih₁ ih₂ =>
      simp only [«def», toFormula_or, BoundedFormula.realize_sup, isWellTyped.or_def,
        schema.or_def] at h_rel h_wt ⊢
      simp_all
      obtain ⟨left, right⟩ := h_wt
      obtain ⟨right, h_wt⟩ := right
      cases h_rel with
      | inl left_1 =>
        have h': ↑q₁.schema ⊆ t.Dom := by simp_all
        have := ih₁ h' left_1
        have h'' : ↑q₁.schema ⊆ ↑(q₁.and q₂).schema := by simp
        apply Or.inl
        exact tuple_restrict left (ih₁ h' left_1) h'' rfl
      | inr right_1 =>
        have h': ↑q₂.schema ⊆ t.Dom := by simp_all
        have := ih₂ h' right_1
        have h'' : ↑q₂.schema ⊆ ↑(q₁.and q₂).schema := by simp
        apply Or.inr
        exact tuple_restrict right (ih₂ h' right_1) h'' rfl

    | not q ih =>
      simp only [«def», toFormula_not, BoundedFormula.realize_not, isWellTyped.not_def,
        schema.not_def] at h_rel h_wt ⊢
      simp_all only [«def», forall_const]
      apply Aesop.BuiltinRules.not_intro
      intro a
      sorry
