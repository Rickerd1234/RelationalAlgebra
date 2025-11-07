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

@[simp]
def TermtoAtt.eq_iff {t₁ t₂ : (fol dbs).Term (String ⊕ Fin n)} (f : (Fin n → String)) (h : f.Injective) (h' : (t₁.varFinsetLeft ∪ t₂.varFinsetLeft) ∩ FRan f = ∅) :
  (TermtoAtt f t₁) = (TermtoAtt f t₂) ↔ t₁ = t₂ := by
    apply Iff.intro
    . intro h''
      have ⟨k₁, hk₁⟩ := Term.cases t₁
      have ⟨k₂, hk₂⟩ := Term.cases t₂
      subst hk₁ hk₂
      simp_all only [Term.var.injEq]
      cases k₁ with
      | inl val =>
        cases k₂ with
        | inl val_1 =>
          subst h''
          simp_all only [TermtoAtt]
        | inr val_2 =>
          subst h''
          simp_all only [reduceCtorEq, TermtoAtt]
          simp at h'
      | inr val_1 =>
        cases k₂ with
        | inl val =>
          subst h''
          simp_all only [reduceCtorEq, TermtoAtt]
          simp at h'
        | inr val_2 =>
          simp_all only [Sum.inr.injEq]
          exact h h''
    . exact congrArg (TermtoAtt f)


noncomputable def renamePairFunc (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (f : Fin n → String) : String → String :=
  renameFunc ra (dite (ra ∈ dbs rn) (λ h => TermtoAtt f (ts (RelationSchema.index h))) (λ _ => ra))

noncomputable def renamePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (f : Fin n → String) : RA.Query String String :=
  .r (renamePairFunc ra ts f) (.R rn)

theorem renamePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} : (renamePair ra ts f).schema dbs = (dbs rn).image (renamePairFunc ra ts f) := rfl

theorem renamePair.isWellTyped_def :
    RA.Query.isWellTyped dbs (renamePair ra ts f) := by
      simp [renamePair, renamePairFunc, rename_func_bijective]

noncomputable def relJoins (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (f : Fin n → String) : RA.Query String String :=
  ras.foldr (λ ra sq => .j (renamePair ra ts f) sq) (.R rn)

theorem relJoins.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relJoins ras ts f).schema dbs = (Finset.biUnion ras.toFinset (λ ra => (renamePair ra ts f).schema dbs) ∪ dbs rn) := by
    simp [relJoins]
    induction ras with
    | nil => simp_all
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, RA.Query.schema.eq_4, List.toFinset_cons, Finset.biUnion_insert,
        Finset.union_assoc]

theorem relJoins.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relJoins ras ts f) := by
      simp [relJoins]
      induction ras with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldr_cons, RA.Query.isWellTyped.eq_4, renamePair.isWellTyped_def, true_and]
        apply ih
        rw [List.toFinset_cons, Finset.insert_subset_iff] at h
        exact h.2

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def relToRA (rn : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n))
  (f : Fin n → String) (rs : Finset String) : RA.Query String String :=
    .p (rs) ((relJoins (RelationSchema.ordering (dbs rn)) ts f).j (adom dbs rs))

theorem relToRA.schema_def : (relToRA dbs rn ts f rs).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA dbs rn ts f rs) := by
    simp [relToRA, relJoins.isWellTyped_def, adom.isWellTyped_def, adom.schema_def]

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
    next n rn => simp [toRA, relToRA.schema_def]
  | all => simp [toRA, allToRA.schema_def]
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
        | R rn => simp [Relations.boundedFormula, toRA, relToRA.isWellTyped_def]

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
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan f) ⊆ rs) (hf : f.Injective) :
    (toRA dbi.schema q f rs brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑rs, BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ f) ∧ t.ran ⊆ dbi.domain} := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, BoundedFormula.Realize]
        simp [Term.bdEqual] at h

        have rs_ne_empty : rs ≠ ∅ := by
          have ⟨k₁, hk₁⟩ := Term.cases t₁
          have ⟨k₂, hk₂⟩ := Term.cases t₂
          subst hk₁ hk₂
          cases k₁ with
          | inl val =>
            simp_all only [nonempty_subtype, Term.varFinsetLeft, Finset.singleton_union, ne_eq]
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [Finset.subset_empty, Finset.insert_ne_empty]
          | inr val =>
            simp_all only [nonempty_subtype, Term.varFinsetLeft, Finset.empty_union, ne_eq]
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [Finset.subset_empty, Finset.union_eq_empty]
            obtain ⟨left, right⟩ := h
            cases k₂ with
            | inl val_1 => simp_all only [Term.varFinsetLeft, Finset.singleton_ne_empty]
            | inr val_2 =>
              simp_all only [Term.varFinsetLeft]
              have : (FRan f).card = 0 := by exact Finset.card_eq_zero.mpr right
              rw [FRan.card_def hf] at this
              . subst this
                exact Fin.elim0 val_2

        ext t
        rename_i inst_1 inst_2 inst_3
        simp_all only [Set.mem_setOf_eq]
        apply Iff.intro
        · intro a
          obtain ⟨left, right⟩ := a
          have ⟨k₁, hk₁⟩ := Term.cases t₁
          have ⟨k₂, hk₂⟩ := Term.cases t₂
          subst hk₁ hk₂
          simp_all only [Term.realize_var]

          have : t.Dom = ↑rs := by
            have := RA.Query.evaluate.validSchema (adom dbi.schema rs) adom.isWellTyped_def t left
            simp [adom.schema_def] at this
            exact this

          apply And.intro
          . use this
            cases k₁ with
            | inl val =>
              cases k₂ with
              | inl
                val_1 =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert,
                  TermtoAtt, Sum.elim_inl, TupleToFun, decidable_dom, eq_mpr_eq_cast]
                congr
              | inr
                val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Finset.singleton_union,
                  TermtoAtt, Sum.elim_inl, TupleToFun,
                  decidable_dom, eq_mpr_eq_cast, Sum.elim_inr, Function.comp_apply]
                congr
            | inr val_1 =>
              cases k₂ with
              | inl
                val =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert, Finset.empty_union,
                  Sum.elim_inr, Sum.elim_inl, TupleToFun, TermtoAtt]
                unfold TupleToFun
                simp
                congr
              | inr
                val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Sum.elim_inr, TermtoAtt]
                unfold TupleToFun
                simp
                congr
          . rw [adom.complete_def rs_ne_empty] at left
            simp at left
            exact left.2
        · intro a
          obtain ⟨w_1, h_2⟩ := a
          obtain ⟨w_1, h_3⟩ := w_1
          apply And.intro
          · rw [adom.complete_def rs_ne_empty]
            simp
            apply And.intro
            · use w_1
            · intro a h'
              exact h_2 h'
          · have ⟨k₁, hk₁⟩ := Term.cases t₁
            have ⟨k₂, hk₂⟩ := Term.cases t₂
            subst hk₁ hk₂
            simp_all only [Term.realize_var]
            cases k₁ with
            | inl val =>
              cases k₂ with
              | inl
                val_1 =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert,
                  Sum.elim_inl, TupleToFun, TermtoAtt]
                rw [Finset.insert_subset_iff, Finset.insert_subset_iff] at h
                ext v
                have h₁ : (t val).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.2.1
                have h₂ : (t val_1).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.1
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]

              | inr
                val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Finset.singleton_union, Sum.elim_inl,
                  Sum.elim_inr, TermtoAtt]
                rw [Finset.insert_subset_iff] at h
                ext v
                have h₁ : (t val).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.1
                have h₂ : (t (f val_2)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.2 FRan.mem_def
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]
            | inr val_1 =>
              cases k₂ with
              | inl
                val =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert, Finset.empty_union,
                  Sum.elim_inr, Sum.elim_inl, TermtoAtt]
                rw [Finset.insert_subset_iff] at h
                have h₁ : (t (f val_1)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.2 FRan.mem_def
                have h₂ : (t val).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.1
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]
              | inr val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Sum.elim_inr, TermtoAtt]
                have h₁ : (t (f val_1)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h FRan.mem_def
                have h₂ : (t (f val_2)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h FRan.mem_def
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]

      | rel R ts =>
        rename_i inst_1 inst_2 inst_3 l
        simp_all only [BoundedFormula.realize_rel]
        obtain ⟨w, h_1⟩ := inst_1
        cases R with
        | R rn =>
          rw [← fol.Rel]
          simp_rw [folStruc_apply_RelMap, fol.Rel, ArityToTuple.def_dite]
          sorry


theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan f) ⊆ rs) (hf : f.Injective) (h_rs_ne : rs ≠ ∅) :
    (toRA dbi.schema q f rs brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑rs, BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ f) ∧ t.ran ⊆ dbi.domain} := by
      induction hq with
      | falsum => simp only [toRA, RA.Query.evaluateT.eq_7, diffT, Set.diff, and_not_self,
        Set.setOf_false, BoundedFormula.Realize, false_and, exists_false]
      | of_isAtomic h_at => exact toRA.evalT_def_IsAtomic h_at h hf

      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]

        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h
        have rsh₁ : q₁.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩
        have rsh₂ : q₂.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩
        rw [RA.Query.evaluateT, RA.Query.evaluateT, ih₁ rsh₁, ih₂ rsh₂]
        rw [diffT, diffT]

        simp_rw [BoundedFormula.realize_imp]

        simp_all only [forall_const, Set.diff, Set.mem_setOf_eq, not_exists,
          not_and, forall_exists_index, not_forall, not_not]
        obtain ⟨left, right⟩ := h
        obtain ⟨left, right_1⟩ := left
        ext t
        simp_all only [Finset.coe_inj, Set.mem_setOf_eq,
          TupleToFun.tuple_eq_self, exists_const]
        apply Iff.intro
        · intro a
          obtain ⟨left_1, right_2⟩ := a
          simp_all only [exists_and_right, exists_prop, and_true, and_imp]
          have t_dom : t.Dom = ↑rs := by
            have := RA.Query.evaluate.validSchema (adom dbi.schema rs) adom.isWellTyped_def t left_1
            simp [adom.schema_def] at this
            exact this
          have t_ran : t.ran ⊆ dbi.domain := by
            rw [adom.complete_def h_rs_ne] at left_1
            simp at left_1
            exact left_1.2
          apply And.intro ?_ t_ran
          use t_dom
          exact λ hq₁ => right_2 t_dom hq₁ t_ran
        · intro a
          obtain ⟨w, h⟩ := a
          apply And.intro
          · rw [adom.complete_def h_rs_ne]
            . simp_all
          · intro x h_1
            simp_all only [exists_and_right, forall_const, and_true, exists_const]

theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsPrenex) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (hf : f.Injective) (h_rs_ne : q.freeVarFinset ∪ FRan f ≠ ∅) :
    (toRA dbi.schema q f (q.freeVarFinset ∪ FRan f) brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑(q.freeVarFinset ∪ FRan f), BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ f) ∧ t.ran ⊆ dbi.domain} := by
        induction hq with
        | of_isQF h => exact evalT_def_IsQF h (by rfl) hf h_rs_ne
        | all hφ ih => sorry
        | ex hφ ih => sorry

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
    simp_all only [freeVarFinset_toPrenex]

    have : ∀t' : String → μ, (t' ∘ Fin.elim0) = (default : Fin 0 → μ) := by intro t'; ext v; exact False.elim (Fin.elim0 v)
    simp_rw [this]
    . simp; sorry
    . simp [Function.Injective]
    . simp; sorry
