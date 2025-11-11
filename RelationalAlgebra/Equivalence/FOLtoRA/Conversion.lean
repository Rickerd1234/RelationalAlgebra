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


noncomputable def renamePairFunc (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : String → String :=
  renameFunc ra (dite (ra ∈ dbs rn) (λ h => TermtoAtt (FreeMap n brs) (ts (RelationSchema.index h))) (λ _ => ra))

noncomputable def renamePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .r (renamePairFunc ra ts brs) (.R rn)

theorem renamePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} : (renamePair ra ts brs).schema dbs = (dbs rn).image (renamePairFunc ra ts brs) := rfl

theorem renamePair.isWellTyped_def :
    RA.Query.isWellTyped dbs (renamePair ra ts brs) := by
      simp [renamePair, renamePairFunc, rename_func_bijective]

noncomputable def relJoins (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  ras.foldr (λ ra sq => .j (renamePair ra ts brs) sq) (.R rn)

theorem relJoins.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relJoins ras ts brs).schema dbs = (Finset.biUnion ras.toFinset (λ ra => (renamePair ra ts brs).schema dbs) ∪ dbs rn) := by
    simp [relJoins]
    induction ras with
    | nil => simp_all
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, RA.Query.schema.eq_4, List.toFinset_cons, Finset.biUnion_insert,
        Finset.union_assoc]

theorem relJoins.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relJoins ras ts brs) := by
      simp [relJoins]
      induction ras with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldr_cons, RA.Query.isWellTyped.eq_4, renamePair.isWellTyped_def, true_and]
        apply ih
        rw [List.toFinset_cons, Finset.insert_subset_iff] at h
        exact h.2

theorem relJoins.evalT_def [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : ras.toFinset ⊆ dbi.schema rn) :
    RA.Query.evaluateT dbi (relJoins ras ts brs) =
    {t | ∃ (h : (t : String →. μ).Dom = dbi.schema rn ∪ (ras).toFinset.image (λ ra => renamePairFunc ra ts brs ra)),
      (Relations.boundedFormula (relations.R rn) ts).Realize (TupleToFun h) (TupleToFun h ∘ (FreeMap n brs)) ∧ (∀ra ∈ ras, t (renamePairFunc ra ts brs ra) = t ra) ∧ t.ran ⊆ dbi.domain
    } := by
      induction ras with
      | nil =>
        ext t
        simp [Set.mem_setOf_eq]
        apply Iff.intro
        · intro h'
          have h_schema := RA.Query.evaluate.validSchema (relJoins [] ts brs) (relJoins.isWellTyped_def h) t h'
          simp [relJoins.schema_def] at h_schema
          apply And.intro
          · use h_schema
            rw [← fol.Rel, folStruc_apply_RelMap]
            simp [relJoins] at h'
            convert h'
            sorry
          · exact RA.Query.evaluateT.dbi_domain (relJoins.isWellTyped_def h) t h'
        · intro a
          obtain ⟨left, right⟩ := a
          obtain ⟨w, h⟩ := left
          simp [relJoins]
          rw [← fol.Rel, folStruc_apply_RelMap] at h
          convert h
          sorry
      | cons hd tl ih => sorry

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def relToRA (rn : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (rs brs : Finset String) : RA.Query String String :=
    .p (rs) ((relJoins (RelationSchema.ordering (dbs rn)) ts brs).j (adom dbs rs))

theorem relToRA.schema_def : (relToRA dbs rn ts rs brs).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA dbs rn ts rs brs) := by
    simp [relToRA, relJoins.isWellTyped_def, adom.isWellTyped_def, adom.schema_def]

theorem relToRA.evalT_def [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) :
    RA.Query.evaluateT dbi (relToRA dbi.schema rn ts rs brs) =
    {t | ∃ (h : (t : String →. μ).Dom = ↑rs), (Relations.boundedFormula (relations.R rn) ts).Realize (TupleToFun h) (TupleToFun h ∘ (FreeMap n brs)) ∧ t.ran ⊆ dbi.domain} := by
      simp_rw [BoundedFormula.realize_rel]
      rw [← fol.Rel]
      simp_rw [folStruc_apply_RelMap, ArityToTuple.def_dite]
      simp only [relToRA, RA.Query.evaluateT, projectionT, joinT, joinSingleT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq, exists_and_right]

      ext t
      rw [relJoins.evalT_def (subset_of_eq (RelationSchema.ordering_eq_toFinset (dbi.schema rn)))]
      simp_all only [Set.mem_setOf_eq]
      simp_all only [BoundedFormula.realize_rel, RelationSchema.ordering_mem, RelationSchema.ordering_eq_toFinset,
        Finset.coe_union, Finset.coe_image, exists_and_right]

      apply Iff.intro
      · intro a
        obtain ⟨w, h_1⟩ := a
        obtain ⟨left, right⟩ := h_1
        obtain ⟨w_1, h_1⟩ := left
        obtain ⟨left, right_1⟩ := h_1
        obtain ⟨left, right_2⟩ := left
        obtain ⟨w_2, h_1⟩ := right_1
        obtain ⟨w_3, h_2⟩ := left
        obtain ⟨left, right_1⟩ := right_2
        obtain ⟨left_1, right_2⟩ := h_1
        apply And.intro
        · apply Exists.intro
          . rw [← fol.Rel, folStruc_apply_RelMap] at h_2
            convert h_2
            simp_all only [ArityToTuple.def_dite]
            split
            next h_1 =>
              rename_i x
              simp_all only [Part.some_inj]
              have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index h_1))
              simp [hk]
              cases k
              next val =>
                have in_rs : val ∈ rs := by
                  apply h
                  simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
                  apply Or.inl
                  use RelationSchema.index h_1
                  simp [hk]
                have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 val := by
                  rw [← PFun.mem_dom, w_3]
                  simp [renamePairFunc]
                  apply Or.inr
                  use RelationSchema.fromIndex (RelationSchema.index h_1)
                  simp [h_1, renameFunc, hk, TermtoAtt]
                simp
                congr
                rw [(right val).1 in_rs]
                rw [(right_2 val).1 v in_w_1]
              next val =>
                have in_rs : (FreeMap n brs val) ∈ rs := by
                  apply h
                  simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, FRan.mem_def, or_true]
                have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 (FreeMap n brs val) := by
                  rw [← PFun.mem_dom, w_3]
                  simp [renamePairFunc]
                  apply Or.inr
                  use RelationSchema.fromIndex (RelationSchema.index h_1)
                  simp [h_1, renameFunc, hk, TermtoAtt]
                simp
                congr
                rw [(right (FreeMap n brs val)).1 in_rs]
                rw [(right_2 (FreeMap n brs val)).1 v in_w_1]
            next h_1 => simp_all only
        · apply fun ⦃a⦄ ha ↦ right_1 ((?_ : t.ran ⊆ w_1.ran) ha)
          simp [PFun.ran]
          intro a_1 x h_1
          use x
          have in_rs : x ∈ rs := by
            by_contra hc
            have := (right x).2 hc
            simp_all
          have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 x := by
            rw [← PFun.mem_dom, w_3]
            simp [renamePairFunc]
            sorry
          rw [← (right_2 x).1 v in_w_1, ← (right x).1 in_rs]
          exact h_1
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w, h_1⟩ := left
        sorry

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

theorem allToRA.evalT_def [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] :
    RA.Query.evaluateT dbi (allToRA dbi.schema q rs) =
    {t | t.ran ⊆ dbi.domain ∧ t.Dom = ↑rs ∧ ∀t' : String →. μ, (t'.ran ⊆ dbi.domain ∧ t'.Dom = ↑(q.schema dbi.schema)) → t' ∉ q.evaluateT dbi → ∃ x, (x ∈ rs → t x = t' x) → x ∉ rs ∧ ¬t x = Part.none} := by
      simp only [allToRA, RA.Query.evaluateT, diffT, Set.diff, adom.complete_def, exists_prop,
        Set.mem_setOf_eq, projectionT, not_exists, not_and, not_forall, and_imp]

      ext t
      simp_all only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro a
        simp_all only [not_false_eq_true, and_self, implies_true]
      · intro a
        simp_all only [and_self, and_true, not_false_eq_true, implies_true]


noncomputable def toRA
  (f : (fol dbs).BoundedFormula String n) (rs brs : Finset String) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt (FreeMap n brs) t₁) (TermtoAtt (FreeMap n brs) t₂) (adom dbs rs)
    | .rel (.R rn) ts => relToRA dbs rn ts rs brs
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ rs brs) (toRA f₂ rs brs))
    | .all sf => allToRA dbs (toRA sf (rs ∪ FRan (FreeMap (n + 1) brs)) brs) rs

theorem toRA.schema_def :
    (toRA dbs φ rs brs).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n rn => simp [toRA, relToRA.schema_def]
  | all => simp [toRA, allToRA.schema_def]
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsAtomic) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q rs brs).isWellTyped dbs := by
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
        simp [Relations.boundedFormula, BoundedFormula.freeVarFinset] at h'
        cases R with
        | R rn => simp [Relations.boundedFormula, toRA, relToRA.isWellTyped_def]

theorem toRA.isWellTyped_def_IsQF [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsQF) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) :
    (toRA dbs q rs brs).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h'
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp only [RA.Query.isWellTyped, RA.Query.schema]
        simp at h'
        have : q₁.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := by grind
        have : q₂.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]

theorem toRA.isWellTyped_def_IsPrenex {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsPrenex) (h' : q.freeVarFinset ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (h'''' : 1 + n + depth q ≤ brs.card)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q (rs ∪ FRan (FreeMap n brs)) brs).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf (by grind)
      | all =>
        simp [toRA]
        simp at h''''
        rename_i inst_1 n_1 φ h_1 h_ih

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by simp [FreeMap]

        apply allToRA.isWellTyped_def
        . rw [sch]
          exact wt
        . simp only [FreeMap, FRan.liftF_union, schema_def, FRan.liftF_sub,
          Finset.union_subset_union_right]

      | ex =>
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp at h' h'' h''''

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by simp [FreeMap]

        simp only [adom.isWellTyped_def, adom.schema_def, allToRA.schema_def, true_and, and_true, *]
        apply allToRA.isWellTyped_def
        . simp only [RA.Query.isWellTyped, adom.isWellTyped_def, wt, adom.schema_def, and_self,
          schema_def, RA.Query.schema]
        . simp_all only [FreeMap, forall_const, FRan.liftF_union,
          RA.Query.schema, adom.schema_def, FRan.liftF_sub, Finset.union_subset_union_right]

theorem toRA.evalT_def_IsAtomic [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (h' : n ≤ brs.card) :
    (toRA dbi.schema q rs brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑rs, BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ (FreeMap n brs)) ∧ t.ran ⊆ dbi.domain} := by
      induction hq with
      | equal t₁ t₂ =>
        simp only [Term.bdEqual, toRA, RA.Query.evaluateT.eq_2, selectionT, BoundedFormula.Realize, exists_and_right]
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
              have : (FRan (FreeMap n brs)).card = 0 := by exact Finset.card_eq_zero.mpr right
              rw [FRan.card_def (FreeMap.inj_n h')] at this
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
          . simp_all
        · intro a
          obtain ⟨w_1, h_2⟩ := a
          obtain ⟨w_1, h_3⟩ := w_1
          apply And.intro
          · simp_all
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
                have h₂ : (t ((FreeMap n brs) val_2)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.2 FRan.mem_def
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]
            | inr val_1 =>
              cases k₂ with
              | inl
                val =>
                simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert, Finset.empty_union,
                  Sum.elim_inr, Sum.elim_inl, TermtoAtt]
                rw [Finset.insert_subset_iff] at h
                have h₁ : (t ((FreeMap n brs) val_1)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.2 FRan.mem_def
                have h₂ : (t val).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h.1
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]
              | inr val_2 =>
                simp_all only [Term.varFinsetLeft, Finset.empty_union, Sum.elim_inr, TermtoAtt]
                have h₁ : (t ((FreeMap n brs) val_1)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h FRan.mem_def
                have h₂ : (t ((FreeMap n brs) val_2)).Dom := by rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1, Finset.mem_coe]; exact h FRan.mem_def
                simp [Part.getOrElse_of_dom, h₁, h₂] at h_3
                rw [Part.eq_of_get_eq_get h₁ h₂ h_3]

      | rel R ts =>
        cases R with
        | R rn =>
          nth_rewrite 1 [Relations.boundedFormula, toRA]
          exact relToRA.evalT_def h


theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (h' : n ≤ brs.card):
    (toRA dbi.schema q rs brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑rs, BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ (FreeMap n brs)) ∧ t.ran ⊆ dbi.domain} := by
      induction hq with
      | falsum => simp only [toRA, RA.Query.evaluateT.eq_7, diffT, Set.diff, and_not_self,
        Set.setOf_false, BoundedFormula.Realize, false_and, exists_false]
      | of_isAtomic h_at => exact toRA.evalT_def_IsAtomic h_at h h'

      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]

        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h
        have rsh₁ : q₁.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩
        have rsh₂ : q₂.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩
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
            rw [adom.complete_def] at left_1
            simp at left_1
            exact left_1.2.2
          apply And.intro ?_ t_ran
          use t_dom
          exact λ hq₁ => right_2 t_dom hq₁ t_ran
        · intro a
          obtain ⟨w, h⟩ := a
          apply And.intro
          · rw [adom.complete_def]
            . simp_all
          · intro x h_1
            simp_all only [exists_and_right, forall_const, and_true, exists_const]

theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsPrenex) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : n + depth q ≤ brs.card) :
    (toRA dbi.schema q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs).evaluateT dbi =
      {t | ∃h : t.Dom = ↑(q.freeVarFinset ∪ FRan (FreeMap n brs)), BoundedFormula.Realize q (TupleToFun h) ((TupleToFun h) ∘ (FreeMap n brs)) ∧ t.ran ⊆ dbi.domain} := by
        induction hq with
        | of_isQF hqf => exact evalT_def_IsQF hqf (by simp) (by grind only)
        | all hφ ih =>
          rename_i n' φ
          simp [toRA, allToRA.evalT_def]
          ext t
          have := ih (by simp at h; grind)
          rw [FRan.FreeMap_lift_union, this]
          sorry
        | ex hφ ih =>
          rename_i n' φ
          simp [toRA, allToRA.evalT_def, Set.diff]
          ext t
          have := ih (by simp at h; grind)
          rw [FRan.FreeMap_lift_union, this]
          simp_all only [nonempty_subtype, Finset.coe_union, exists_and_right, Set.mem_setOf_eq, and_true]
          apply Iff.intro
          · intro a
            simp_all only [exists_true_left, and_true]
            obtain ⟨left, right⟩ := a
            obtain ⟨left, right_1⟩ := left
            have this : n' < (RelationSchema.ordering brs).length := by simp at h; simp; grind
            use (t ((RelationSchema.ordering brs).get ⟨n', this⟩)).get (by sorry)
            simp_all only [implies_true, depth, zero_le, sup_of_le_left, List.get_eq_getElem]
            sorry
          · intro a
            simp_all only [and_true, forall_const]
            obtain ⟨left, right⟩ := a
            obtain ⟨w_1, h_1⟩ := left
            obtain ⟨w_2, h_1⟩ := h_1
            simp_all only [forall_const, true_and]
            haveI : ∀a, Decidable (t a).Dom := λ a ↦ Classical.propDecidable (t a).Dom
            use λ a => ite ((t a).Dom) (t a) (ite (a = (RelationSchema.ordering brs)[n]?) (w_2) (Part.none))
            simp_all only [implies_true, depth, zero_le, sup_of_le_left, Part.coe_some, PFun.dom_mk,
              left_eq_ite_iff]
            split_ands
            . sorry
            . simp [adom.schema_def, Part.dom_iff_mem, FreeMap, liftF]
              ext a
              sorry
            . intro a a_1
              simp [← Finset.coe_union, FRan.FreeMap_lift_union]
              sorry
            . intro x
              split
              all_goals
                apply And.intro
                · intro a a_1
                  cases a with
                  | inl h_4 => rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1] at a_1; simp_all
                  | inr h_5 => rw [Part.dom_iff_mem, ← PFun.mem_dom, w_1] at a_1; simp_all
                · intro a a_1
                  rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, w_1]; simp_all

-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs (toPrenex q) q.schema (FreshAtts (toPrenex q))

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.schema_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan.default = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, ← this]
    refine toRA.isWellTyped_def_IsPrenex ?_ ?_ ?_ ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp
    . simp
    . have ⟨k, hk⟩ := FreshAtts.card_def q.toFormula.toPrenex
      rw [hk]
      grind only

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] [Nonempty μ] (q : FOL.Query dbi.schema) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q ∩ {t | t.ran ⊆ dbi.domain} := by
    rw [FOL.Query.evaluateT, Set.ext_iff]
    intro t
    rw [@Set.mem_inter_iff]
    rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
    rw [fol_to_ra_query, BoundedQuery.schema, toPrenex]
    have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan (FreeMap 0 (FreshAtts (BoundedQuery.toFormula q).toPrenex)) = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp [FreeMap]
    rw [← freeVarFinset_toPrenex, ← this, toRA.evalT_def_IsPrenex hq]
    rw [Set.mem_setOf_eq]
    simp only [BoundedFormula.realize_toPrenex]
    simp_all only [freeVarFinset_toPrenex]

    have : ∀t' : String → μ, (t' ∘ Fin.elim0) = (default : Fin 0 → μ) := by intro t'; ext v; exact False.elim (Fin.elim0 v)
    simp_rw [FreeMap, this]
    . simp
    . have ⟨k, hk⟩ := FreshAtts.card_def q.toFormula.toPrenex
      rw [hk]
      grind only
