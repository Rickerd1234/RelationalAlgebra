import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.AttBuilder
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.RealizeProperties

open RM FOL FirstOrder Language

variable {μ : Type}

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula String n :=
  q.toFormula.toPrenex

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp

@[simp]
def BoundedFormula.safeR (f : fol.Relations l) (dbs : String → Finset String) : Prop :=
  match f with
  | FOL.relations.R dbs' rn => dbs = dbs'

@[simp]
def BoundedFormula.safeDBS (f : fol.BoundedFormula Attribute n) (dbs : String → Finset String) : Prop :=
  match f with
  | .falsum => True
  | .rel R _ => safeR R dbs
  | .equal _ _ => True
  | .imp f₁ f₂ => safeDBS f₁ dbs ∧ safeDBS f₂ dbs
  | .all f' => safeDBS f' dbs

@[simp]
theorem BoundedFormula.safeDBS_ToPrenex (q : fol.BoundedFormula Attribute n) : BoundedFormula.safeDBS q.toPrenex dbs ↔ BoundedFormula.safeDBS q dbs := by
  induction q with
  | falsum =>
    simp_all only [safeDBS, BoundedFormula.toPrenex]
  | equal =>
    simp_all only [safeDBS, BoundedFormula.toPrenex, Term.bdEqual]
  | imp =>
    simp_all only [safeDBS]
    simp [BoundedFormula.toPrenex]
    sorry
  | _ => aesop

@[simp]
theorem BoundedQuery.safeDBS (q : FOL.BoundedQuery dbs n) : BoundedFormula.safeDBS q.toFormula dbs := by
  induction q with
  | _ => aesop

@[simp]
theorem BoundedQuery.safeDBS_toPrenex (q : FOL.BoundedQuery dbs n) : BoundedFormula.safeDBS q.toFormula.toPrenex dbs := by
  simp_all only [BoundedFormula.safeDBS_ToPrenex, safeDBS]

noncomputable def TermtoAtt : fol.Term (String ⊕ Fin n) → String ⊕ Fin n
  | var v => v
  | _ => Sum.inl (Classical.arbitrary String)

section toRA

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def tsToRenameFunc (ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)) (a : String ⊕ Fin n) : String ⊕ Fin n :=
  a.elim (λ s => dite (s ∈ dbs rn) (λ h => TermtoAtt (ts (RelationSchema.index h))) (λ _ => a)) (λ _ => a)

def filterLast : (String ⊕ Fin (n + 1)) → Prop := (Sum.elim (λ _ => True) (λ v => v ≠ Fin.last n))

@[simp]
theorem filterLast.inl_def : filterLast (n := n) (Sum.inl a) = True := rfl

@[simp]
theorem filterLast.inr_def_ne_last {v : Fin (n + 1)} (h : v ≠ Fin.last n) : filterLast (Sum.inr v) = True := by
  simp [filterLast, h]

@[simp]
theorem filterLast.inr_def_eq_last {v : Fin (n + 1)} (h : v = Fin.last n) : filterLast (Sum.inr v) = False := by
  simp [filterLast, h]

instance DecidableFilterLast :
  DecidablePred (α := String ⊕ Fin (n + 1)) filterLast := by
  intro a
  cases a with
  | inl val =>
    simp_all only [filterLast, ne_eq, Sum.elim_inl]
    exact instDecidableTrue
  | inr val_1 =>
    simp_all only [filterLast, ne_eq, Sum.elim_inr]
    exact instDecidableNot

@[simp]
theorem filterLast.mem_inl_def {rs : Finset (String ⊕ Fin (n + 1))} : (Sum.inl x) ∈ rs.filter filterLast ↔ (Sum.inl x) ∈ rs := by simp

@[simp]
theorem filterLast.mem_inr_def {rs : Finset (String ⊕ Fin (n + 1))} : (Sum.inr v) ∈ rs.filter filterLast ↔ v ≠ Fin.last n ∧ Sum.inr v ∈ rs := by
  rw [@Finset.mem_filter, ne_eq]
  by_cases h : v = Fin.last n
  . simp_all only [inr_def_eq_last, and_false, not_true_eq_false, false_and]
  . simp_all only [filterLast.inr_def_ne_last h, and_true, not_false_eq_true, true_and]

noncomputable def castSum {n} : (String ⊕ Fin (n + 1)) → (String ⊕ Fin n) :=
  Sum.elim (Sum.inl) (λ v => dite (v = Fin.last n) (λ _ => Sum.inl (Classical.arbitrary String)) (Sum.inr ∘ v.castPred))

@[simp]
theorem castFilterLast.inl_def : castSum (n := n) (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem castFilterLast.inr_def_ne_last {v : Fin (n + 1)} (h : v ≠ Fin.last n) : castSum (Sum.inr v) = (Sum.inr (v.castPred h)) := by
  simp [castSum, h]

@[simp]
theorem castFilterLast.inr_def_eq_last {v : Fin (n + 1)} (h : v = Fin.last n) : castSum (Sum.inr v) = Sum.inl (Classical.arbitrary String) := by
  simp [castSum, h]

noncomputable def forgetLast (rs : Finset (String ⊕ Fin (n + 1))) : Finset (String ⊕ Fin n) :=
  (rs.filter filterLast).image castSum

@[simp]
theorem forgetLast.ext_iff_inl : Sum.inl x ∈ forgetLast rs ↔ Sum.inl x ∈ rs := by
  simp_all [forgetLast]
  intro x_1 a_1 a_2 a_3
  rename_i n
  by_cases x_1 = Fin.last n
  . simp_all
  . simp_all

@[simp]
theorem forgetLast.ext_iff_inr {rs : Finset (String ⊕ Fin (n + 1))} : Sum.inr x ∈ forgetLast rs ↔ Sum.inr x.castSucc ∈ rs ∧ x.castSucc ≠ Fin.last n := by
  simp_all [forgetLast]
  by_cases hc : x.castSucc = Fin.last n
  . simp_all
  . apply Iff.intro
    . intro h
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      rw [castFilterLast.inr_def_ne_last right_1] at right
      simp [← Sum.inr_injective right, left]
    . simp_all
      intro a
      use x.castSucc
      simp_all only [ne_eq, Fin.castSucc_ne_last, not_false_eq_true, filterLast.inr_def_ne_last, and_self,
        castFilterLast.inr_def_ne_last, Fin.castPred_castSucc]

noncomputable def castQ : RA.Query String (String ⊕ Fin (n + 1)) → RA.Query String (String ⊕ Fin n)
  | .R rn => .R rn
  | .s a b q => .s (castSum a) (castSum b) (castQ q)
  | .p rs q => .p (rs.image castSum) (castQ q)
  | .j q₁ q₂ => .j (castQ q₁) (castQ q₂)
  | .r f q => .r (λ a => (f (a.map id Fin.castSucc)).elim (Sum.inl) (castSum ∘ Sum.inr)) (castQ q)
  | .d q nq => .d (castQ q) (castQ nq)
  | .u q₁ q₂ => .u (castQ q₁) (castQ q₂)

noncomputable def allToRA
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]
    (rs : Finset (String ⊕ Fin n)) (q' : RA.Query String (String ⊕ Fin (n + 1))) : RA.Query String (String ⊕ Fin n) :=
      (adom ((Finset.image Sum.inl) ∘ dbs) rs).d (castQ (.p (rs.image (Sum.map id Fin.castSucc)) q'))

theorem allToRA.freeVarFinset_def [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] {rs : Finset (String ⊕ Fin n)} :
    (allToRA dbs rs φ).schema ((Finset.image Sum.inl) ∘ dbs) = rs := by
  induction φ with
  | R =>
    simp [allToRA]
    exact adom.schema_def
  | _ => expose_names; exact a_ih

noncomputable def toRA
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]
  (rs : Finset (String ⊕ Fin n)) (f : fol.BoundedFormula String n) : RA.Query String (String ⊕ Fin n) :=
    match f with
    | .falsum => .d (adom ((Finset.image Sum.inl) ∘ dbs) rs) (adom ((Finset.image Sum.inl) ∘ dbs) rs)
    | .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (adom ((Finset.image Sum.inl) ∘ dbs) rs)
    | .rel (.R dbs rn) ts => .p rs (.r (tsToRenameFunc dbs ts) (.R rn))
    | .imp f₁ f₂ => .d (adom ((Finset.image Sum.inl) ∘ dbs) rs) (.d (toRA rs f₁) (toRA rs f₂))
    | .all f => allToRA dbs rs (toRA (rs.image (Sum.map id Fin.castSucc)) f)

theorem toRA.freeVarFinset_def [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] {rs : Finset (String ⊕ Fin n)} :
    (toRA dbs rs φ).schema ((Finset.image Sum.inl) ∘ dbs) = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n dbs rn =>
      simp [toRA]
  | all =>
    simp [toRA];
    exact allToRA.freeVarFinset_def dbs
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : fol.BoundedFormula String n}
  (hq : q.IsAtomic) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset.image Sum.inl ⊆ rs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs rs q).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, adom.isWellTyped_def]
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂
        split_ands
        all_goals(
          simp [adom.schema_def, TermtoAtt]; simp [Term.bdEqual] at h'
        )
        . cases k₁ with
          | inl s => aesop
          | inr i => exact False.elim (Fin.elim0 i)
        . cases k₂ with
          | inl s => aesop
          | inr i => exact False.elim (Fin.elim0 i)
      | rel R ts =>
        cases R with
        | R dbs rn =>
          simp [Relations.boundedFormula, toRA] at h h' ⊢
          subst h
          apply And.intro
          . sorry
          . rw [Finset.subset_iff]
            rename_i inst_7
            intro x a
            simp_all only [nonempty_subtype, Finset.mem_image, exists_exists_and_eq_and]
            obtain ⟨w, h⟩ := inst_7
            cases x with
            | inl s =>
              have : ∀a, ¬(tsToRenameFunc dbs ts (Sum.inl a) = Sum.inl s) := by sorry
              simp_rw [this]
              sorry
            | inr i => exact False.elim (Fin.elim0 i)

theorem toRA.isWellTyped_def_IsQF {q : fol.BoundedFormula String n}
  (hq : q.IsQF) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset.image Sum.inl ⊆ rs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)] [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]:
    (toRA dbs rs q).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h h'
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp [Finset.image_union q₁.freeVarFinset q₂.freeVarFinset] at h'
        have : q₁.freeVarFinset.image Sum.inl ⊆ rs := Finset.union_subset_left h'
        have : q₂.freeVarFinset.image Sum.inl ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.freeVarFinset_def]

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset.image Sum.inl ⊆ rs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)] [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] :
    (toRA dbs rs q).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf h h'
      | all =>
        simp [toRA, toRA.freeVarFinset_def]
        simp_all
      | ex =>
        simp at h ⊢
        simp [toRA, adom.isWellTyped_def, toRA.freeVarFinset_def, adom.schema_def]
        simp_all

theorem toRA.evalT_def_IsPrenex [folStruc dbi (μ := μ)] {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbi.schema) [Fintype (adomRs dbi.schema)] :
    (toRA dbi.schema q.freeVarFinset q).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' q.freeVarFinset} := by
        induction hq with
        | _ => sorry --unfold toRA; aesop; all_goals (try simp_all [Set.diff, BoundedFormula.Realize]); all_goals sorry;


-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs q.schema (toPrenex q)

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.freeVarFinset_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex]
    refine toRA.isWellTyped_def_IsPrenex ?_ (BoundedQuery.safeDBS_toPrenex q) ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Nonempty μ] (q : FOL.Query dbi.schema) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q := by
    rw [FOL.Query.evaluateT, Set.ext_iff]
    intro t
    rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
    rw [fol_to_ra_query, BoundedQuery.schema, toPrenex]
    have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
    have h_safe := BoundedQuery.safeDBS_toPrenex q
    rw [← freeVarFinset_toPrenex, toRA.evalT_def_IsPrenex hq h_safe]
    rw [Set.mem_setOf_eq]
    simp only [BoundedFormula.realize_toPrenex]
    simp_all only [BoundedFormula.safeDBS_ToPrenex, BoundedQuery.safeDBS, freeVarFinset_toPrenex,
      exists_and_right]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      refine Exists.intro rfl ?_
      rw [← BoundedQuery.Realize] at left ⊢
      obtain ⟨vs, left⟩ := left
      have : vs = default := by ext v; exact False.elim (Fin.elim0 v)
      subst this
      refine (BoundedQuery.Realize.restrict ?_ ?_).mp left
      . rw [freeVarFinset_toPrenex]
      . rw [freeVarFinset_toPrenex, BoundedQuery.schema]
    · intro a
      obtain ⟨w, h⟩ := a
      use TupleToFun w
      apply And.intro ?_
      . ext a v
        rw [PFun.mem_res]
        simp_all only [Finset.mem_coe, TupleToFun]
        simp_rw [Set.ext_iff, PFun.mem_dom t, ← Part.dom_iff_mem, Finset.mem_coe] at w
        apply Iff.intro
        · intro a_1
          have ta_dom : (t a).Dom := (PFun.mem_dom t a).mpr (Exists.intro v a_1)
          apply And.intro
          · simp_all
          · simp [Part.getOrElse, ta_dom, Part.get_eq_of_mem a_1 ta_dom]
        · intro a_1
          obtain ⟨left, right⟩ := a_1
          subst right
          rw [← w a] at left
          simp [Part.getOrElse, left, Part.get_mem]
      . use default
        rw [← BoundedQuery.Realize] at h ⊢
        have : ∀x x' t, x = x' → (q.Realize dbi x t → q.Realize dbi x' t) := by simp
        apply (this (TupleToFun ?_) (TupleToFun w) default ?_) h
        . simp [w]
        . simp [w]
