import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.WellTyped
import RelationalAlgebra.FOL.Relabel

open FOL FirstOrder Language RM Term

namespace FOL

def Term.realizeSome (dbi) [folStruc dbi] {n : ℕ} (t : fol.Term (Attribute ⊕ (Fin n))) (tup : Tuple) (iv : Fin n →. Value) : Prop
  := (t.realize (Sum.elim tup iv)).Dom

@[simp]
theorem Term.realizeSome.def (dbi) [folStruc dbi] (t : fol.Term (Attribute ⊕ (Fin n))) (tup : Tuple) (iv : Fin n →. Value) :
  Term.realizeSome dbi t tup iv ↔ (t.realize (Sum.elim tup iv)).Dom := by rfl

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

-- Formal realization definition, requires all terms to be 'some'
def BoundedQuery.Realize (dbi) {n : ℕ} [folStruc dbi] : BoundedQuery n → Tuple → (Fin n →. Value) → Prop
  | R dbs rn tMap,  tup, iv => (∀i, Term.realizeSome dbi (tMap i) tup iv) ∧ (R dbs rn tMap).toFormula.Realize tup iv
  | tEq q t₁ t₂,    tup, iv => q.Realize dbi tup iv ∧ Term.realizeSome dbi t₁ tup iv ∧ Term.realizeSome dbi t₂ tup iv
                                ∧ (BoundedFormula.equal t₁ t₂).Realize tup iv
  | and q₁ q₂,      tup, iv => q₁.Realize dbi tup iv ∧ q₂.Realize dbi tup iv
  | ex q,           tup, iv => ∃a, q.Realize dbi tup (Fin.snoc iv a)

@[simp]
theorem BoundedQuery.Realize.R_def [folStruc dbi] {n : ℕ} (tMap) {tup : Tuple} {iv : Fin n →. Value}
  : (R dbs rn tMap).Realize dbi tup iv ↔ (∀i, Term.realizeSome dbi (tMap i) tup iv) ∧ (R dbs rn tMap).toFormula.Realize tup iv := by
    rfl

theorem BoundedQuery.Realize.all_i_R_def [folStruc dbi] {n : ℕ} (tMap) {tup : Tuple} {iv : Fin n →. Value}
  : (R dbs rn tMap).Realize dbi tup iv → (∀i, ((tMap i).realize (Sum.elim tup iv)).Dom) := by
    simp_all

theorem BoundedQuery.Realize.all_att_R_def [folStruc dbi] {n : ℕ} (tMap) {tup : Tuple} {iv : Fin n →. Value}
  : (R dbs rn tMap).Realize dbi tup iv → (∀a (ha : a ∈ dbs rn), ((tMap ((dbs rn).index ha)).realize (Sum.elim tup iv)).Dom) := by
    simp_all

theorem BoundedQuery.Realize.exists_att_R_def [folStruc dbi] {n : ℕ} (tMap) {tup : Tuple} {iv : Fin n →. Value} (h : dbs rn ≠ ∅)
  : (R dbs rn tMap).Realize dbi tup iv → (∃t' : fol.Term (Attribute ⊕ (Fin n)), (t'.realize (Sum.elim tup iv)).Dom) := by
    intro a
    simp_all only [ne_eq, R_def, realizeSome.def, toFormula_rel, BoundedFormula.realize_rel]
    obtain ⟨left, right⟩ := a
    induction h' : (dbs rn).card with
    | zero => simp_all only [Finset.card_eq_zero]
    | succ k ih =>
      use (tMap (Fin.cast h'.symm (Fin.ofNat' (k + 1) (k + 1))))
      simp_all only

@[simp]
theorem BoundedQuery.Realize.exists_tuple_R_def [folStruc dbi] {n : ℕ} (tMap) {tup : Tuple} {iv : Fin n →. Value}
  : (R dbi.schema rn tMap).Realize dbi tup iv → (∃t' ∈ (dbi.relations rn).tuples, ∀i, (tMap i).realize (Sum.elim tup iv) = t' ((dbi.schema rn).fromIndex i)) := by
    intro a
    simp_all only [R_def, realizeSome.def, toFormula_rel, BoundedFormula.realize_rel, folStruc_apply_RelMap]
    obtain ⟨left, right⟩ := a
    use (ArityToTuple fun i ↦ realize (Sum.elim tup iv) (tMap i))
    simp_all only [true_and]
    intro i
    simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def, and_self]

@[simp]
theorem BoundedQuery.Realize.tEq_def [folStruc dbi] {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) {tup : Tuple} {iv : Fin n →. Value}
  : (tEq q t₁ t₂).Realize dbi tup iv ↔ (q.Realize dbi tup iv ∧ Term.realizeSome dbi t₁ tup iv ∧ Term.realizeSome dbi t₂ tup iv ∧ (BoundedFormula.equal t₁ t₂).Realize tup iv) := by
    rfl

@[simp]
theorem BoundedQuery.Realize.and_def [folStruc dbi] {n : ℕ} (q₁ q₂ : BoundedQuery n) {t : Tuple} {iv : Fin n →. Value}
  : (and q₁ q₂).Realize dbi t iv ↔ q₁.Realize dbi t iv ∧ q₂.Realize dbi t iv := by
    rfl

@[simp]
theorem BoundedQuery.Realize.ex_def [folStruc dbi] {n : ℕ} (q : BoundedQuery (n + 1)) {t: Tuple} {iv : Fin n →. Value}
  : (ex q).Realize dbi t iv ↔ ∃a, q.Realize dbi t (Fin.snoc iv a) := by
    rfl

@[simp]
theorem BoundedQuery.Realize.exs_def [folStruc dbi] {n : ℕ} (q : BoundedQuery n) {t: Tuple}
  : (exs q).Realize dbi t (default : Fin 0 →. Value) ↔ ∃iv : Fin n →. Value, q.Realize dbi t iv := by
    induction' n with n ih
    · simp
      apply Iff.intro
      · intro a
        use default
      · intro a
        obtain ⟨w, h⟩ := a
        have hw : w = default := by
          ext a v
          exact Fin.elim0 a
        simp_all only
    · simp only [BoundedQuery.exs, ih, BoundedQuery.Realize.ex_def]
      constructor
      ·
        intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨w_1, h⟩ := h
        apply Exists.intro
        · exact h
      · intro a
        obtain ⟨w, h_1⟩ := a
        use Fin.init w
        use (w (Fin.last n))
        simp_all only [Part.some_get, Fin.snoc_init_self, and_true]

@[simp]
theorem BoundedQuery.Realize.schema_sub_Dom [folStruc dbi] {n : ℕ} {q : BoundedQuery n} {t : Tuple} {iv : Fin n →. Value}
  : q.Realize dbi t iv → ∀a ∈ q.schema, (t a).Dom := by
    induction q with
    | R dbs rn vs =>
      intro a_1 a_2 a_3
      simp_all only [R_def, realizeSome.def, toFormula_rel, BoundedFormula.realize_rel, schema.R_def, Set.mem_toFinset,
        Set.mem_setOf_eq]
      obtain ⟨left, right⟩ := a_1
      obtain ⟨w, h⟩ := a_3
      have z := Term.cases (vs w)
      simp_all only [Sum.exists]
      cases z with
      | inl h_1 =>
        obtain ⟨w_1, h_1⟩ := h_1
        simp_all only [varFinsetLeft.eq_1, Finset.mem_singleton]
        subst h
        have z' := left w
        simp_all only [realize_var, Sum.elim_inl]
      | inr h_2 =>
        obtain ⟨w_1, h_1⟩ := h_2
        simp_all only [varFinsetLeft.eq_2, Finset.not_mem_empty]

    | _ => aesop

@[simp]
theorem Relmap.tuple_restrict [folStruc : folStruc dbi] {t t' : Tuple} {tMap : Fin (dbi.schema rn).card → fol.Term (Attribute ⊕ (Fin n))}:
  folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim t' iv) (tMap i)) →
  (h : t'.Dom ⊆ t.Dom) → t' = t.restrict h →
  (∀ (i : Fin (Finset.card (dbi.schema rn))), (realize (Sum.elim (PFun.restrict t h) iv) (tMap i)).Dom) →
    folStruc.RelMap (fol.Rel dbi.schema rn) (fun i ↦ realize (Sum.elim t iv) (tMap i)) := by
      intro ht h ht' hdom
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
            have z := hdom (RelationSchema.index h_1)
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
theorem BoundedQuery.Realize.tuple_restrict [folStruc dbi] {n : ℕ} {q : BoundedQuery n} {t : Tuple} {iv : Fin n →. Value} (h_wt : q.isWellTyped dbi.schema)
  : q.Realize dbi t' iv → (h : t'.Dom ⊆ t.Dom) →  t' = t.restrict h → q.Realize dbi t iv := by
    intro a h a_1
    induction q with
    | R dbs rn tMap =>
      simp_all only [R_def, realizeSome.def, toFormula_rel, BoundedFormula.realize_rel]
      obtain ⟨left, right⟩ := a
      apply And.intro
      · intro i
        exact Term.realizeSome.tuple_restrict (tMap i) (left i) h rfl
      · simp_all
        subst h_wt
        exact Relmap.tuple_restrict right h rfl left

    | tEq sq t₁ t₂ ih  =>
      simp_all only [tEq_def, true_and]
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_2, right⟩ := right
      apply And.intro
      . exact ih h_wt.1 left
      . apply And.intro
        · exact Term.realizeSome.tuple_restrict t₁ left_1 h rfl
        · apply And.intro
          · exact Term.realizeSome.tuple_restrict t₂ left_2 h rfl
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
                  exact Part.dom_iff_mem.mp left_2
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
                  exact Part.dom_iff_mem.mp left_2
                . simp_all
              | inr fin₂ =>
                simp_all

    | ex q ih =>
      simp at a ⊢ h_wt
      have ⟨w, hw⟩ := a
      use w
      simp_all only [forall_const]

    | _ => aesop

@[simp]
theorem Relmap.tuple_restrict2 [folStruc : folStruc dbi] {t : Tuple} (h : ↑((BoundedQuery.R dbi.schema rn tMap).schema) ⊆ t.Dom) :
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
theorem BoundedQuery.Realize.tuple_restrict2 [folStruc dbi] {n : ℕ} {q : BoundedQuery n} {t : Tuple} {iv : Fin n →. Value} (h_wt : q.isWellTyped dbi.schema)
  : (h : ↑q.schema ⊆ t.Dom) → q.Realize dbi t iv → q.Realize dbi (t.restrict h) iv := by
    intro h h_rel
    induction q with
    | R dbs rn tMap =>
      simp_all only [isWellTyped.R_def, R_def, toFormula_rel, BoundedFormula.realize_rel]
      obtain ⟨left, right⟩ := h_rel
      apply And.intro
      · intro i
        have z : ↑(tMap i).varFinsetLeft ⊆ t.Dom := by rw [@Set.subset_def] at ⊢ h; aesop
        have z' := Term.realizeSome.tuple_restrict2 (tMap i) (left i) z (rfl)
        have hz' : ↑(tMap i).varFinsetLeft ⊆ ↑(R dbs rn tMap).schema := by simp [Set.subset_def]; intro x hx; use i
        exact realizeSome.tuple_restrict (tMap i) z' hz' rfl
      · subst h_wt
        simp_all [Relmap.tuple_restrict2 h right]


    | tEq sq t₁ t₂ ih  =>
      simp_all only [isWellTyped.tEq_def, tEq_def, forall_const]
      obtain ⟨left, right⟩ := h_rel
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_2, right⟩ := right
      have ⟨t₁, ht₁⟩ := Term.cases t₁
      subst ht₁
      have ⟨t₂, ht₂⟩ := Term.cases t₂
      subst ht₂
      simp_all only [realizeSome.def, realize_var, true_and]
      obtain ⟨left_3, right_1⟩ := h_wt
      obtain ⟨left_4, right_1⟩ := right_1
      cases t₁ with
      | inl val =>
        cases t₂ with
        | inl val_1 =>
          simp_all only [Sum.elim_inl, hasSafeTerm_mem_schema]
          apply And.intro
          · exact left_4
          · apply And.intro
            · exact right_1
            · ext a : 1
              simp_all only [Part.dom_iff_mem, BoundedFormula.Realize, realize_var, Sum.elim_inl,
                schema, PFun.mem_restrict, Finset.mem_coe, true_and]
        | inr val_2 =>
          simp_all only [Sum.elim_inl, hasSafeTerm_mem_schema, Sum.elim_inr, true_and]
          apply And.intro
          · exact left_4
          · simp_all only [BoundedFormula.Realize, realize_var, Sum.elim_inl, Sum.elim_inr]
            ext a : 1
            simp_all only [PFun.mem_restrict, schema.tEq_def, Finset.mem_coe, true_and]
      | inr val_1 =>
        cases t₂ with
        | inl val =>
          simp_all only [Sum.elim_inr, Sum.elim_inl, hasSafeTerm_mem_schema, true_and]
          apply And.intro
          · exact right_1
          · ext a : 1
            simp_all only [Part.dom_iff_mem, BoundedFormula.Realize, realize_var, Sum.elim_inr,
              Sum.elim_inl, schema, PFun.mem_restrict, Finset.mem_coe, true_and]
        | inr val_2 =>
          simp_all only [Sum.elim_inr, true_and]
          exact right

    | and q₁ q₂ ih₁ ih₂ =>
      simp_all only [isWellTyped.and_def, and_self, and_def, forall_const]
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
      simp_all only [isWellTyped.ex_def, ex_def, Part.coe_some, forall_const]
      obtain ⟨w, h_1⟩ := h_rel
      apply Exists.intro
      · apply @ih
        simp_all only [schema.ex_def, forall_true_left]
        apply h_1

theorem BoundedQuery.Realize.mapTermRel_add_castLe {dbi} [struc : folStruc dbi] {k : ℕ}
    {ft : ∀ n, fol.Term (Attribute ⊕ (Fin n)) → fol.Term (Attribute ⊕ (Fin (k + n)))}
    {n} {φ : BoundedQuery n} (v : ∀ {n}, (Fin (k + n) →. Value) → Attribute →. Value)
    {v' : Tuple} (xs : Fin (k + n) →. Value)
    (h1 :
      ∀ (n) (t : fol.Term (Attribute ⊕ (Fin n))) (xs' : Fin (k + n) →. Value),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (hv : ∀ (n) (xs : Fin (k + n) →. Value) (x : Part Value), @v (n + 1) (Fin.snoc xs x : Fin _ →. Value) = v xs) :
    (φ.mapTermRel ft fun _ => BoundedQuery.castLE (add_assoc _ _ _).symm.le).Realize dbi v' xs ↔
      φ.Realize dbi (v xs) (xs ∘ Fin.natAdd _) := by
        induction φ with
        | R => simp [FOL.BoundedQuery.mapTermRel, h1]
        | tEq q t₁ t₂ ih =>
          rename_i n'
          simp [FOL.BoundedQuery.mapTermRel, h1, hv, ih]
          intro a a_1 a_2
          have ⟨t₁, ht₁⟩ := Term.cases t₁
          have ⟨t₂, ht₂⟩ := Term.cases t₂
          simp_all only [realize_var, BoundedFormula.Realize]
        | and _ _ ih1 ih2 => simp [FOL.BoundedQuery.mapTermRel, ih1, ih2]
        | ex _ ih => simp [FOL.BoundedQuery.mapTermRel, ih, hv]

@[simp]
theorem BoundedQuery.Realize.relabel_def {dbi} [folStruc dbi] {m n : ℕ} {φ : BoundedQuery n}  {g : Attribute → Attribute ⊕ (Fin m)} {t : Tuple}
  {xs : Fin (m + n) →. Value} :
  (φ.relabel g).Realize dbi t xs ↔
    φ.Realize dbi (Sum.elim t (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
      apply BoundedQuery.Realize.mapTermRel_add_castLe <;> simp

@[simp]
theorem BoundedQuery.Realize.all_terms {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery n} {t : Tuple} {xs : Fin n →. Value} :
  φ.Realize dbi t xs → ∀term, φ.hasSafeTerm term → (term.realize (Sum.elim t xs)).Dom := by
    induction φ with
    | ex q ih =>
      intro a term a_1
      simp_all only [ex_def, hasSafeTerm.ex_def]
      obtain ⟨w, h⟩ := a
      have z := ih h ((Term.relabel (Sum.map id (Fin.castLE (by simp))) term)) a_1
      simp_all only [Part.dom_iff_mem, realize_relabel]
      obtain ⟨z, hz⟩ := z
      use z
      have ⟨z', hz'⟩ := Term.cases term
      subst hz'
      cases z'
      . simp_all
      . simp_all [Fin.snoc]
        exact hz

    | _ => aesop

@[simp]
theorem BoundedQuery.Realize.tuple_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery n} {t t' : Tuple} {xs : Fin n →. Value} :
  t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs) := by
    intro h
    rw [h]

@[simp]
theorem BoundedQuery.Realize.assignment_eq_ext {dbi} [folStruc dbi] {n : ℕ} {φ : BoundedQuery n} {t t' : Tuple} {xs xs' : Fin n →. Value} :
  xs = xs' → t = t' → (φ.Realize dbi t xs ↔ φ.Realize dbi t' xs') := by
    intro h h'
    rw [h, h']

-- -- Realize a query, without any additional attributes in the 'tuple'
nonrec def Query.RealizeDom (φ : Query) (dbi : DatabaseInstance) [folStruc dbi] (t : Tuple) : Prop :=
  φ.Realize dbi t default ∧ t.Dom ⊆ φ.schema

@[simp]
theorem Query.RealizeDom.def [folStruc dbi] (φ : Query)
  : φ.RealizeDom dbi t ↔ BoundedQuery.Realize dbi φ t default ∧ t.Dom ⊆ φ.schema := by rfl

theorem Query.RealizeDom.schema_sub_Dom [folStruc dbi] {q : FOL.Query} (h: q.RealizeDom dbi t) :
  ↑q.schema ⊆ t.Dom := by simp_all; exact BoundedQuery.Realize.schema_sub_Dom h.1

@[simp]
theorem Query.RealizeDom.imp_Realize {t dbi} [folStruc dbi] (φ : Query) :
    φ.RealizeDom dbi t → φ.Realize dbi t default := by
      simp_all

@[simp]
theorem Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema {t dbi} [folStruc dbi]
    (φ : Query) (h_dom_schema : t.Dom ⊆ ↑φ.schema) :
    φ.Realize dbi t default → φ.RealizeDom dbi t := by
      simp_all
