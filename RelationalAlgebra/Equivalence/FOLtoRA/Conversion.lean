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
def RealizeDomSet {dbi : DatabaseInstance String String μ} [folStruc dbi] [Nonempty μ]
  (q : (fol dbi.schema).BoundedFormula String n) (rs brs : Finset String) (t : String →. μ) (h : t.Dom = rs) : Prop :=
    q.Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) ∧ t.ran ⊆ dbi.domain

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
    {t | ∃h,
      RealizeDomSet (μ := μ)
        (Relations.boundedFormula (relations.R rn) ts)
        (dbi.schema rn ∪ (ras).toFinset.image (λ ra => renamePairFunc ra ts brs ra))
        brs t h
      ∧ (∀ra ∈ ras, t (renamePairFunc ra ts brs ra) = t ra)
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

theorem relToRA.evalT_def [Nonempty (adomRs dbi.schema)] [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) :
    RA.Query.evaluateT dbi (relToRA dbi.schema rn ts rs brs) =
    {t | ∃h, RealizeDomSet (μ := μ) (Relations.boundedFormula (relations.R rn) ts) rs brs t h} := by
      simp_rw [RealizeDomSet, BoundedFormula.realize_rel]
      rw [← fol.Rel]
      simp_rw [folStruc_apply_RelMap, ArityToTuple.def_dite]
      simp only [relToRA, RA.Query.evaluateT, projectionT, joinT, joinSingleT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq, exists_and_right]

      ext t
      rw [relJoins.evalT_def (subset_of_eq (RelationSchema.ordering_eq_toFinset (dbi.schema rn)))]
      simp_all only [Set.mem_setOf_eq]
      simp_all only [RealizeDomSet, BoundedFormula.realize_rel, RelationSchema.ordering_mem, RelationSchema.ordering_eq_toFinset,
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
        obtain ⟨left, right_1⟩ := w_3
        obtain ⟨left_1, right_2⟩ := h_1
        apply And.intro
        · apply Exists.intro
          . rw [← fol.Rel, folStruc_apply_RelMap] at right_1
            apply (congr_arg (λ x => x ∈ (dbi.relations rn).tuples) ?_).mp right_1
            . intro left right_1
              ext x
              simp_all only [PFun.mem_dom, Finset.mem_coe]
              apply Iff.intro
              · intro a
                obtain ⟨w_4, h_1⟩ := a
                by_contra hc
                rw [(right x).2 hc] at h_1
                simp_all
              · intro a
                simp_all only
                have w_2_Dom := RA.Query.evaluate.validSchema (adom dbi.schema rs) adom.isWellTyped_def w_2 left
                rw [adom.schema_def] at w_2_Dom
                rw [← Finset.mem_coe, ← w_2_Dom, PFun.mem_dom] at a
                obtain ⟨v, hv⟩ := a
                rw [(right_1 x).2.1 v hv]
                use v
            . funext x
              simp_all only [ArityToTuple.def_dite]
              by_cases hc : x ∈ dbi.schema rn
              . simp_all only [↓reduceDIte, Part.some_inj]
                have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index hc))
                simp [hk]
                cases k
                next val =>
                  have in_rs : val ∈ rs := by
                    apply h
                    simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
                    apply Or.inl
                    use RelationSchema.index hc
                    simp [hk]
                  have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 val := by
                    rw [← PFun.mem_dom, left]
                    simp [renamePairFunc]
                    apply Or.inr
                    use RelationSchema.fromIndex (RelationSchema.index hc)
                    simp [hc, renameFunc, hk, TermtoAtt]
                  simp
                  congr
                  rw [(right val).1 in_rs]
                  rw [(right_2 val).1 v in_w_1]
                next val =>
                  have in_rs : (FreeMap n brs val) ∈ rs := by
                    apply h
                    simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, FRan.mem_def, or_true]
                  have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 (FreeMap n brs val) := by
                    rw [← PFun.mem_dom, left]
                    simp [renamePairFunc]
                    apply Or.inr
                    use RelationSchema.fromIndex (RelationSchema.index hc)
                    simp [hc, renameFunc, hk, TermtoAtt]
                  simp
                  congr
                  rw [(right (FreeMap n brs val)).1 in_rs]
                  rw [(right_2 (FreeMap n brs val)).1 v in_w_1]
              . simp_all only [↓reduceDIte]
        · simp at left_1
          have : t.ran ⊆ w_2.ran := by
            simp [PFun.ran]
            intro v x hv
            have in_rs : x ∈ rs := by
              by_contra hc
              have := (right x).2 hc
              simp_all
            have ⟨v', in_w_2⟩ : ∃v, v ∈ w_2 x := by
              rw [← PFun.mem_dom, left_1.1]
              exact in_rs
            use x
            rw [← (right_2 x).2.1 v' in_w_2, ← (right x).1 in_rs]
            exact hv
          rw [@Set.subset_def]
          apply λ a ha => left_1.2 (this ha)
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w, h_1⟩ := left
        sorry

noncomputable def toRA
  (f : (fol dbs).BoundedFormula String n) (rs brs : Finset String) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt (FreeMap n brs) t₁) (TermtoAtt (FreeMap n brs) t₂) (adom dbs rs)
    | .rel (.R rn) ts => relToRA dbs rn ts rs brs
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ rs brs) (toRA f₂ rs brs))
    | .all sf => (adom dbs rs).d (.p rs ((adom dbs (rs ∪ FRan (FreeMap (n + 1) brs))).d (toRA sf (rs ∪ FRan (FreeMap (n + 1) brs)) brs)))

theorem toRA.schema_def :
    (toRA dbs φ rs brs).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n rn => simp [toRA, relToRA.schema_def]
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

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        simp only [FreeMap, FRan.liftF_sub, Finset.union_subset_union_right]

      | ex =>
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp at h' h'' h''''

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by simp [FreeMap]

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        simp only [FreeMap, FRan.liftF_sub, Finset.union_subset_union_right]

theorem toRA.falsum_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] :
    (toRA dbi.schema (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs).evaluateT dbi =
      {t | ∃h, RealizeDomSet (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs t h} := by
        ext t
        simp [toRA, RA.Query.evaluateT.eq_7, diffT, Set.diff, adom.complete_def, exists_prop,
          Set.mem_setOf_eq, not_and, RealizeDomSet, BoundedFormula.Realize, false_and, exists_false,
          iff_false, Classical.not_imp, not_not, imp_self]

theorem toRA.term_equal_def [Nonempty μ] [folStruc dbi (μ := μ)] {t₁ t₂ : (fol dbi.schema).Term (String ⊕ Fin n)} {t : String →. μ} {rs : Finset String}
  (h : t.Dom = ↑rs) (h' : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs):
    t (TermtoAtt (FreeMap n brs) t₁) = t (TermtoAtt (FreeMap n brs) t₂) ↔
      (BoundedFormula.equal t₁ t₂).Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) := by
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂

        cases k₁
        all_goals (
          cases k₂
          all_goals (
            -- Rewrite ... ⊆ rs
            simp only [Term.bdEqual, BoundedFormula.freeVarFinset, Term.varFinsetLeft, Finset.insert_union, ← h,
              Finset.singleton_union, Finset.subset_iff, ← Finset.mem_coe, Finset.coe_insert, Set.mem_insert_iff,
              forall_eq_or_imp, Finset.empty_union, PFun.mem_dom, ← Part.dom_iff_mem] at h'

            -- Prepare for `TupleToFun.tuple_eq_iff`
            apply Iff.symm
            rw [TermtoAtt, TermtoAtt]
            simp only [BoundedFormula.Realize, Term.realize_var, Sum.elim_inl, Sum.elim_inr, Function.comp]

            -- Complete the proof
            apply TupleToFun.tuple_eq_iff h
            . simp_all only [Finset.mem_coe, FRan.mem_def]
            . simp_all only [Finset.mem_coe, FRan.mem_def]
          )
        )

theorem toRA.equal_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [Fintype ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {t₁ t₂ : (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs) :
    (toRA dbi.schema (t₁ =' t₂) rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet (t₁ =' t₂) rs brs t h} := by
      simp_rw [Term.bdEqual, toRA, RA.Query.evaluateT, selectionT]
      simp_rw [RealizeDomSet]

      rw [adom.complete_def]
      ext t
      simp_rw [exists_prop, Set.mem_setOf_eq, exists_and_right]

      apply Iff.intro
      . intro ⟨⟨w_1, h_2⟩, right⟩
        apply And.intro (Exists.intro w_1 ((term_equal_def w_1 h).mp right)) h_2
      . intro ⟨⟨w_1, h_2⟩, right⟩
        exact And.intro (And.intro w_1 right) ((term_equal_def w_1 h).mpr h_2)

theorem toRA.imp_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)]
  (ih₁ : (toRA dbi.schema q₁ rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet q₁ rs brs t h})
  (ih₂ : (toRA dbi.schema q₂ rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet q₂ rs brs t h}) :
    (toRA dbi.schema (q₁.imp q₂) rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet (q₁.imp q₂) rs brs t h} := by
      ext t
      simp only [toRA, RA.Query.evaluateT.eq_7, diffT, Set.diff, adom.complete_def, exists_prop,
        Set.mem_setOf_eq, RA.Query.evaluateT, not_and, not_not, RealizeDomSet,
        BoundedFormula.realize_imp, exists_and_right]
      simp_all only [nonempty_subtype, RealizeDomSet, Finset.coe_inj, exists_and_right,
        Set.mem_setOf_eq, and_true, and_imp, forall_exists_index, exists_true_left,
        TupleToFun.tuple_eq_self]
      apply Iff.intro
      · intro a_1
        simp_all only [Finset.coe_inj, TupleToFun.tuple_eq_self, implies_true, exists_const, and_self]
      · intro ⟨⟨w_1, h_1⟩, right⟩
        simp_all only [Finset.coe_inj, TupleToFun.tuple_eq_self, implies_true, and_self]

theorem toRA.not_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [Fintype ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)]
  (ih : (toRA dbi.schema q rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet q rs brs t h}) :
    (toRA dbi.schema q.not rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet (q.not) rs brs t h} := by
      exact imp_def ih falsum_def

theorem toRA.all_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] {q : (fol dbi.schema).BoundedFormula String (n + 1)}
  (ih : (toRA dbi.schema q (rs ∪ FRan (FreeMap (n + 1) brs)) brs).evaluateT dbi = {t | ∃h, RealizeDomSet q (rs ∪ FRan (FreeMap (n + 1) brs)) brs t h}) :
    (toRA dbi.schema q.all rs brs).evaluateT dbi = {t | ∃h, RealizeDomSet (q.all) rs brs t h} := by
      simp [toRA, Set.diff]
      ext t
      sorry
      -- aesop?

theorem toRA.evalT_def_IsAtomic [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (h' : n ≤ brs.card) :
    (toRA dbi.schema q rs brs).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | equal t₁ t₂ => exact equal_def h
      | rel R ts =>
        cases R with
        | R rn =>
          nth_rewrite 1 [Relations.boundedFormula, toRA]
          exact relToRA.evalT_def h


theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (h' : n ≤ brs.card):
    (toRA dbi.schema q rs brs).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | falsum => exact falsum_def
      | of_isAtomic h_at => exact toRA.evalT_def_IsAtomic h_at h h'

      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h

        exact toRA.imp_def (ih₁ (Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩)) (ih₂ (Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩))


theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsPrenex) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : n + depth q < brs.card) (h' : brs ∩ q.freeVarFinset = ∅) :
    (toRA dbi.schema q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs).evaluateT dbi =
      {t | ∃h, RealizeDomSet q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs t h} := by
        induction hq with
        | of_isQF hqf => exact evalT_def_IsQF hqf (fun ⦃a⦄ a ↦ a) (by grind only)

        | all hφ ih =>
          apply all_def

          simp_rw [Finset.union_assoc, FRan.FreeMap_lift_union]
          simp [← Nat.add_assoc] at h

          exact ih h h'

        | ex hφ ih =>
          apply not_def ∘ all_def ∘ not_def

          simp_rw [Finset.union_assoc, FRan.FreeMap_lift_union, BoundedFormula.freeVarFinset, Finset.union_empty] at h' ⊢
          simp [← Nat.add_assoc] at h

          exact ih h h'


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
    simp only [BoundedFormula.realize_toPrenex, RealizeDomSet]
    simp_all only [freeVarFinset_toPrenex]

    have : ∀t' : String → μ, (t' ∘ Fin.elim0) = (default : Fin 0 → μ) := by intro t'; ext v; exact False.elim (Fin.elim0 v)
    simp_rw [FreeMap, this]
    . simp
    . have ⟨k, hk⟩ := FreshAtts.card_def q.toFormula.toPrenex
      rw [hk]
      grind only
    . simp
