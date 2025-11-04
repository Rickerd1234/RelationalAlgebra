import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.FreshAtts
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RealizeProperties

open RM FOL FirstOrder Language

variable {μ : Type}

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : (fol dbs).BoundedFormula String n :=
  q.toFormula.toPrenex

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp

section toRA

noncomputable def TermtoAtt (f : (Fin n → String)) : (fol dbs).Term (String ⊕ Fin n) → String
  | var (Sum.inl s) => s
  | var (Sum.inr i) => f i
  | _ => Classical.arbitrary String

noncomputable def relSelect (ra : String) (sq : RA.Query String String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (f : Fin n → String) : RA.Query String String :=
  .s ra (dite (ra ∈ dbs rn) (λ h => TermtoAtt f (ts (RelationSchema.index h))) (λ _ => ra)) sq

theorem relSelect.schema_def : (relSelect ra q ts f).schema dbs = q.schema dbs := rfl

theorem relSelect.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : RA.Query.isWellTyped dbs q) (h' : ra ∈ q.schema dbs)
  (h'' : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan f ⊆ q.schema dbs) :
    RA.Query.isWellTyped dbs (relSelect ra q ts f) := by
      simp [relSelect]
      simp_all only [true_and]
      split
      next h_1 =>
        have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index h_1))
        simp [hk]
        cases k
        . simp [TermtoAtt];
          rw [Finset.union_subset_iff, Finset.subset_iff] at h''
          obtain ⟨left, right⟩ := h''
          apply left
          simp_rw [Finset.mem_biUnion, Finset.mem_univ, true_and]
          use RelationSchema.index h_1
          simp [hk]
        . simp [TermtoAtt]; apply h''; simp
      next h_1 => simp_all only

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def relSelects (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (f : Fin n → String) (rs : Finset String) : RA.Query String String :=
  ras.foldr (λ ra sq => relSelect ra sq ts f) ((adom dbs rs).j (.R rn))

theorem relSelects.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relSelects dbs ras ts f rs).schema dbs = rs ∪ dbs rn := by
    simp [relSelects]
    induction ras with
    | nil => simp [adom.schema_def]
    | cons hd tl ih =>
      simp_all only [List.foldr_cons]
      exact ih

theorem relSelects.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} [Nonempty ↑(adomRs dbs)]
  (h : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ dbs rn ∪ FRan f ⊆ rs) (h': ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relSelects dbs ras ts f rs) := by
      simp [relSelects]
      induction ras with
      | nil => simp; apply adom.isWellTyped_def
      | cons hd tl ih =>
        simp
        apply relSelect.isWellTyped_def
        . apply ih
          simp_rw [Finset.subset_iff, List.mem_toFinset, List.mem_cons] at h' ⊢
          intro a h
          exact h' (Or.inr h)
        . rw [← relSelects, relSelects.schema_def, Finset.mem_union]
          simp_rw [Finset.subset_iff, List.mem_toFinset, List.mem_cons] at h'
          apply Or.inl (h ?_)
          rw [Finset.mem_union]
          simp_all
        . rw [← relSelects, relSelects.schema_def, Finset.subset_iff]
          intro a h'
          rw [Finset.mem_union]
          apply Or.inl
          apply h
          grind

noncomputable def relToRA (rn : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n))
  (f : Fin n → String) (rs : Finset String) : RA.Query String String :=
    .p (rs) (relSelects dbs (RelationSchema.ordering (dbs rn)) ts f (rs ∪ dbs rn))

theorem relToRA.schema_def : (relToRA dbs rn ts f rs).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} [Nonempty ↑(adomRs dbs)] (h : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan f ⊆ rs) : RA.Query.isWellTyped dbs (relToRA dbs rn ts f rs) := by
  simp [relToRA]
  apply And.intro
  · apply relSelects.isWellTyped_def dbs (rn := rn)
    . grind
    . simp
  · simp [relSelects.schema_def]

noncomputable def allToRA (q' : RA.Query String String) (rs : Finset String) : RA.Query String String :=
  (adom dbs rs).d (.p rs ((adom dbs (q'.schema dbs)).d q'))

theorem allToRA.schema_def : (allToRA dbs q rs).schema dbs = rs := by
  induction q with
  | R =>
    simp [allToRA]
    exact adom.schema_def
  | _ => expose_names; exact a_ih

theorem allToRA.isWellTyped_def (h : q.isWellTyped dbs) (h' : rs ⊆ q.schema dbs) [Nonempty ↑(adomRs dbs)] :
  (allToRA dbs q rs).isWellTyped dbs := by
    simp [allToRA]
    simp_all only [nonempty_subtype, and_self, adom.isWellTyped_def, adom.schema_def]

noncomputable def toRA
  (f : (fol dbs).BoundedFormula String n) (f' : Fin n → String) (rs brs : Finset String) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt f' t₁) (TermtoAtt f' t₂) (adom dbs rs)
    | .rel (.R rn) ts => relToRA dbs rn ts f' rs
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ f' rs brs) (toRA f₂ f' rs brs))
    | .all sf => allToRA dbs (toRA sf (liftF f' brs) (rs ∪ FRan (liftF f' brs)) brs) rs

theorem toRA.schema_def :
    (toRA dbs φ f rs brs).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n rn =>
      simp [toRA, relToRA.schema_def]
  | all =>
    simp [toRA]
    apply allToRA.schema_def dbs
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsAtomic) (f : Fin n → String) (h' : (q.freeVarFinset ∪ FRan f) ⊆ rs)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q f rs brs).isWellTyped dbs := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, adom.isWellTyped_def]
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂
        split_ands
        all_goals(
          simp [Term.bdEqual] at h'
          simp [adom.schema_def, TermtoAtt]
          rename_i inst_1
          simp_all only [nonempty_subtype]
          obtain ⟨w, h_1⟩ := inst_1
          cases k₁ with
          | inl val =>
            cases k₂ with
            | inl
              val_1 =>
              simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert]
              grind
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.empty_union, Finset.singleton_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
          | inr val_1 =>
            cases k₂ with
            | inl
              val =>
              simp_all only [Term.varFinsetLeft, Finset.singleton_union,
                Finset.union_insert, Finset.empty_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.empty_union]
              simp [FRan, FRanS] at *
              try simp_all [Set.subset_def]
        )
      | rel R ts =>
        cases R with
        | R rn =>
          simp [Relations.boundedFormula, toRA] at h' ⊢
          apply relToRA.isWellTyped_def
          grind

theorem toRA.isWellTyped_def_IsQF [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsQF) (f : Fin n → String) (h' : (q.freeVarFinset ∪ FRan f) ⊆ rs) :
    (toRA dbs q f rs brs).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at f h'
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp only [RA.Query.isWellTyped, RA.Query.schema]
        simp at h'
        have : q₁.freeVarFinset ∪ FRan f ⊆ rs := by grind
        have : q₂.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]

theorem toRA.isWellTyped_def_IsPrenex {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsPrenex) (h' : q.freeVarFinset ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (h''' : (FRan (liftF f brs)) ⊆ brs) (h'''' : brs.card ≥ 1 + n + depth q)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q f (rs ∪ FRan f) brs).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf f (by grind)
      | all =>
        simp [toRA]
        simp at h''''
        rename_i inst_1 n_1 φ h_1 h_ih

        have wt := h_ih (f := (liftF f brs)) h' h'' (FRan.liftF_sub_brs (by grind) h''') (by grind)
        have sch : rs ∪ FRan f ⊆ (toRA dbs φ (liftF f brs) (rs ∪ FRan (liftF f brs)) brs).schema dbs := by
          simp_all [schema_def dbs]
          exact Finset.union_subset_union_right FRan.liftF_sub

        simp_all [allToRA.isWellTyped_def]

      | ex =>
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp at h' h'' h''''

        have wt := h_ih (f := (liftF f brs)) h' h'' (FRan.liftF_sub_brs (by grind) h''') (by grind)
        have sch : rs ∪ FRan f ⊆ (toRA dbs φ (liftF f brs) (rs ∪ FRan (liftF f brs)) brs).schema dbs := by
          simp_all [schema_def dbs]
          exact Finset.union_subset_union_right FRan.liftF_sub

        simp only [adom.isWellTyped_def, true_and, *]
        apply And.intro
        · apply And.intro
          . simp_all [allToRA.isWellTyped_def, schema_def, RA.Query.isWellTyped, adom.isWellTyped_def,
              adom.schema_def, and_self, RA.Query.schema]
          · rfl
        · rfl

theorem toRA.evalT_def_IsAtomic [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan f) ⊆ rs) :
    (toRA dbi.schema q f rs brs).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' rs} := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, BoundedFormula.Realize]
        simp [Term.bdEqual] at h
        ext t
        rename_i inst_1 inst_2 inst_3
        simp_all only [nonempty_subtype, Set.mem_setOf_eq]
        obtain ⟨w, h_1⟩ := inst_1
        apply Iff.intro
        · intro a
          obtain ⟨left, right⟩ := a
          obtain ⟨left, right_1⟩ := left
          obtain ⟨w_1, h_2⟩ := right_1
          obtain ⟨left_1, right_1⟩ := h_2
          obtain ⟨w_2, h_2⟩ := right_1
          obtain ⟨left_2, right_1⟩ := h_2
          sorry
        · intro a
          obtain ⟨w_1, h_2⟩ := a
          obtain ⟨left, right⟩ := h_2
          obtain ⟨w_2, h_2⟩ := left
          subst right
          apply And.intro
          · apply And.intro
            · rfl
            · sorry
          · have ⟨k₁, hk₁⟩ := Term.cases t₁
            have ⟨k₂, hk₂⟩ := Term.cases t₂
            subst hk₁ hk₂
            simp_all only [Term.realize_var]
            cases k₁ with
            | inl val =>
              cases k₂ with
              | inl
                val_1 =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert, Sum.elim_inl, TermtoAtt]
                rw [Finset.insert_subset_iff, Finset.insert_subset_iff] at h
                ext v
                simp [h.1, h.2, PFun.mem_res, h_2]
              | inr
                val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Finset.singleton_union, Sum.elim_inl,
                  Sum.elim_inr, TermtoAtt]
                rw [Finset.insert_subset_iff] at h
                ext v
                simp [h.1, PFun.mem_res, h_2]
                apply Iff.intro
                . intro a
                  subst a
                  obtain ⟨left, right⟩ := h
                  apply And.intro
                  · exact right FRan.mem_def
                  · rw [← h_2]
                    congr
                    sorry
                . intro a
                  obtain ⟨left, right⟩ := h
                  obtain ⟨left_1, right_1⟩ := a
                  subst right_1
                  sorry
            | inr val_1 =>
              cases k₂ with
              | inl
                val =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert, Finset.empty_union,
                  Sum.elim_inr, Sum.elim_inl]
                sorry
              | inr val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Sum.elim_inr]
                sorry

      | rel R ts =>
        rename_i inst_1 inst_2 inst_3 l
        simp_all only [BoundedFormula.realize_rel, exists_and_right]
        obtain ⟨w, h_1⟩ := inst_1
        cases R with
        | R rn =>
          sorry


theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan f) ⊆ rs) :
    (toRA dbi.schema q f rs brs).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' rs} := by
      induction hq with
      | falsum => simp_all only [BoundedFormula.freeVarFinset, Finset.empty_union, toRA,
          RA.Query.evaluateT.eq_7, diffT, Set.diff, and_not_self, Set.setOf_false,
          BoundedFormula.Realize, false_and, exists_const]
      | of_isAtomic h_at => exact evalT_def_IsAtomic h_at h
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]

        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h
        have rsh₁ : q₁.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩
        have rsh₂ : q₂.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩
        rw [RA.Query.evaluateT, RA.Query.evaluateT, ih₁ rsh₁, ih₂ rsh₂]
        rw [diffT, diffT]

        simp_rw [BoundedFormula.realize_imp]

        simp_all only [exists_and_right, forall_const, Set.diff, Set.mem_setOf_eq, not_exists,
          not_and, forall_exists_index, not_forall, not_not, and_imp]
        obtain ⟨left, right⟩ := h
        obtain ⟨left, right_1⟩ := left
        ext
        rename_i x
        simp_all only [exists_prop, exists_and_right, Set.mem_setOf_eq]
        apply Iff.intro
        · intro a
          obtain ⟨left_1, right_2⟩ := a
          sorry
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_1, right_2⟩ := h
          obtain ⟨w_1, h⟩ := left_1
          subst right_2
          apply And.intro
          · sorry
          · intro x x_1 h_1 a
            use w
            apply exists_and_right.mp
            use w_1
            simp [a]
            apply h
            sorry


theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsPrenex) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] :
    (toRA dbi.schema q f (q.freeVarFinset ∪ FRan f) brs).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' (q.freeVarFinset ∪ FRan f)} := by
        induction hq with
        | of_isQF h =>
          rw [evalT_def_IsQF h]
          . simp only [Finset.coe_union, exists_and_right]
          . simp

        | all => sorry
        | ex => sorry

-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs (toPrenex q) Fin.elim0 q.schema (FreshAtts (toPrenex q))

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.schema_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan.default = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, ← this]
    refine toRA.isWellTyped_def_IsPrenex ?_ ?_ ?_ ?_ ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp
    . simp
    . apply FRan.liftF_sub_brs
      . have ⟨k, hk⟩ := FreshAtts.card_def (f := q.toFormula.toPrenex)
        rw [hk]
        grind only
      . exact Finset.inter_eq_left.mp rfl
    . have ⟨k, hk⟩ := FreshAtts.card_def (f := q.toFormula.toPrenex)
      rw [hk]
      grind only

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] [Nonempty μ] (q : FOL.Query dbi.schema) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q := by
    rw [FOL.Query.evaluateT, Set.ext_iff]
    intro t
    rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
    rw [fol_to_ra_query, BoundedQuery.schema, toPrenex]
    have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan Fin.elim0 = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp
    rw [← freeVarFinset_toPrenex, ← this, toRA.evalT_def_IsPrenex hq]
    rw [Set.mem_setOf_eq]
    simp only [BoundedFormula.realize_toPrenex]
    simp_all only [freeVarFinset_toPrenex, exists_and_right]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      simp_rw [FRan.default_eq_empty, Finset.coe_empty, Set.union_empty]
      apply Exists.intro rfl ?_
      rw [← BoundedQuery.Realize] at left ⊢
      obtain ⟨vs, left⟩ := left
      have : vs = default := by ext v; exact False.elim (Fin.elim0 v)
      subst this
      apply (BoundedQuery.Realize.restrict ?_ ?_).mp left
      . simp [freeVarFinset_toPrenex]
      . simp [freeVarFinset_toPrenex, BoundedQuery.schema]
    · intro a
      obtain ⟨w, h⟩ := a
      use TupleToFun w
      apply And.intro ?_
      . ext a v
        rw [PFun.mem_res]
        simp_all only [TupleToFun]
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
          rw [FRan.default_eq_empty, Finset.coe_empty, Set.union_empty, Finset.mem_coe, ← w a] at left
          simp [Part.getOrElse, left, Part.get_mem]
      . use default
        rw [← BoundedQuery.Realize] at h ⊢
        have : ∀x x' t, x = x' → (q.Realize dbi x t → q.Realize dbi x' t) := by simp
        apply (this (TupleToFun ?_) (TupleToFun w) default ?_) h
        . simp [w]
        . simp [w]
