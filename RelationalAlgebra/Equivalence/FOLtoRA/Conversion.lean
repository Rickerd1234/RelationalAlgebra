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

noncomputable def TermtoAtt (brs : Finset String) : (fol dbs).Term (String ⊕ Fin n) → String
  | var (Sum.inl s) => s
  | var (Sum.inr i) => FreeMap n brs i
  | _ => Classical.arbitrary String


noncomputable def TermfromAtt {brs : Finset String} (hn : n ≤ brs.card) : String → (fol dbs).Term (String ⊕ Fin n) :=
  λ a => dite (a ∈ FRan (FreeMap n brs)) (inVar ∘ Fin.castLE (by rw [FreeMap.FRan_card_def hn]) ∘  RelationSchema.index) (λ _ => outVar a)

theorem TermfromAtt.TermtoAtt_inv {hn : n ≤ brs.card} : TermtoAtt brs ∘ TermfromAtt hn (dbs := dbs) = id := by
  ext a
  simp [TermfromAtt, TermtoAtt]
  split
  next x s heq =>
    split at heq
    next h => simp_all only [Term.var.injEq, reduceCtorEq]
    next h => simp_all only [Term.var.injEq, Sum.inl.injEq]
  next x i heq =>
    split at heq
    next h =>
      simp_all only [Term.var.injEq, Sum.inr.injEq]
      subst heq
      exact FreeMap.self_def_cast (Eq.mpr_prop (Eq.refl (a ∈ FRan (FreeMap n brs))) h) hn (Nat.le_refl n)
    next h => simp_all only [Term.var.injEq, reduceCtorEq]
  next x x_1 x_2 =>
    simp_all only [imp_false]
    split at x_1
    next h =>
      split at x_2
      next h_1 =>
        simp_all only [Term.var.injEq, reduceCtorEq, not_false_eq_true, implies_true, Sum.inr.injEq, forall_eq']
      next h_1 => simp_all only [Term.var.injEq, reduceCtorEq, not_false_eq_true, implies_true, not_true_eq_false]
    next h =>
      split at x_2
      next h_1 => simp_all only [not_true_eq_false]
      next h_1 => simp_all only [not_false_eq_true, Term.var.injEq, Sum.inl.injEq, forall_eq']

theorem TermtoAtt.TermfromAtt_inv (hn : n ≤ brs.card) (h' : ∀t : (fol dbs).Term (String ⊕ Fin n), t.varFinsetLeft ∩ FRan (FreeMap n brs) = ∅) :
  TermfromAtt hn (dbs := dbs) ∘ TermtoAtt brs = id := by
    ext t
    simp [TermfromAtt, TermtoAtt]
    have ⟨k, hk⟩ := Term.cases t
    have := h' t
    subst hk
    cases k
    next a =>
      simp_all [Finset.eq_empty_iff_forall_notMem]
    next i =>
      simp [FreeMap.index_self _ hn, Fin.castLE_of_eq (FreeMap.FRan_card_def hn),
          Fin.cast_cast, Fin.cast_eq_self]

@[simp]
def RealizeDomSet {dbi : DatabaseInstance String String μ} [folStruc dbi] [Nonempty μ]
  (q : (fol dbi.schema).BoundedFormula String n) (rs brs : Finset String) (t : String →. μ) (h : t.Dom = rs) : Prop :=
    q.Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) ∧ t.ran ⊆ dbi.domain

@[simp]
def TermtoAtt.eq_iff {t₁ t₂ : (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} (h : n ≤ brs.card) (h' : (t₁.varFinsetLeft ∪ t₂.varFinsetLeft) ∩ FRan (FreeMap n brs) = ∅) :
  (TermtoAtt brs t₁) = (TermtoAtt brs t₂) ↔ t₁ = t₂ := by
    have h := FreeMap.inj_n h
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
    . exact congrArg (TermtoAtt brs)


noncomputable def renamer {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (ra : String) : String :=
  ((RelationSchema.index? (dbs rn) ra).map (TermtoAtt brs ∘ ts)).getD ra

noncomputable def getRAs (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) : Finset String :=
  (dbs rn).filter (λ ra => renamer ts brs ra = a)

theorem getRAs.mem_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {a : String} :
  ra ∈ getRAs ts brs a ↔ ra ∈ dbs rn ∧ renamer ts brs ra = a := by simp [getRAs]

noncomputable instance {dbs} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} : Fintype ↑{ra | ra ∈ dbs rn ∧ renamer ts brs ra = a} := by
  apply Fintype.ofFinset (getRAs ts brs a)
  intro ra
  simp [Set.mem_setOf_eq.mp getRAs.mem_def]

theorem getRAs.def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {a : String} :
  getRAs ts brs a = {ra | ra ∈ dbs rn ∧ renamer ts brs ra = a} := by simp [getRAs]

theorem getRAs.renamer_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) (h : getRAs ts brs a ≠ ∅) :
  (getRAs ts brs a).image (λ ra => renamer ts brs ra) = {a} := by
    ext a'
    simp_rw [← Finset.mem_coe, Finset.coe_image, getRAs.def]
    simp [ne_eq, Finset.ext_iff, getRAs.mem_def] at h
    simp_all only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_singleton, Set.mem_singleton_iff]
    obtain ⟨w, ⟨left, right⟩⟩ := h
    subst right
    apply Iff.intro
    · intro ⟨w_1, left_1, right⟩
      subst right
      simp_all only
    · intro a_1
      subst a_1
      use w

noncomputable def renamePairFunc (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : String → String :=
  renameFunc ra (renamer ts brs ra)

theorem getRAs.renamePair_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) (h : getRAs ts brs a ≠ ∅) :
  (getRAs ts brs a).image (λ ra => renamePairFunc ra ts brs ra) = {a} := by
    simp_rw [renamePairFunc, renameFunc.old_def]
    exact renamer_def ts brs a h

theorem getRAs.biUnion_renamePairFunc_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) :
  Finset.biUnion ((dbs rn).image (λ ra => renamePairFunc ra ts brs ra)) (λ a => (getRAs ts brs a)) = dbs rn := by
    ext a'
    simp_all only [Finset.mem_biUnion, Finset.mem_image, mem_def, exists_eq_right_right',
      and_iff_right_iff_imp]
    intro ha'
    use a'
    apply And.intro ha' renameFunc.old_def

noncomputable def renamePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .r (renamePairFunc ra ts brs) (.R rn)

theorem renamePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (renamePair ra ts brs).schema dbs = (dbs rn).image (renamePairFunc ra ts brs) := rfl

theorem renamePair.isWellTyped_def :
    RA.Query.isWellTyped dbs (renamePair ra ts brs) := by
      simp [renamePair, renamePairFunc, rename_func_bijective]

theorem renamePair.evalT_def [Fintype (adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
    RA.Query.evaluateT dbi (renamePair ra ts brs) =
      {t | t ∘ (renamePairFunc ra ts brs) ∈ (dbi.relations rn).tuples} := by
        simp [renamePair]
        rfl


noncomputable def combinePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .s ra (renamePairFunc ra ts brs ra) (.j (.p {renamePairFunc ra ts brs ra} (renamePair ra ts brs)) (.p {ra} (.R rn)))

theorem combinePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (combinePair ra ts brs).schema dbs = {ra, renamePairFunc ra ts brs ra} := by simp [combinePair]

theorem combinePair.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ra ∈ dbs rn) :
    RA.Query.isWellTyped dbs (combinePair ra ts brs) := by
      simp [combinePair, renamePair.isWellTyped_def, renamePair.schema_def, h]
      use ra


theorem combinePair.evalT_def [Fintype (adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
    (hra : ra ∈ dbi.schema rn) :
    RA.Query.evaluateT dbi (combinePair ra ts brs) =
      {t : String →. μ | ∃t₁ ∈ (dbi.relations rn).tuples, ∃t₂, t₂ ∘ (renamePairFunc ra ts brs) ∈ (dbi.relations rn).tuples ∧
          (t ra = t (renamePairFunc ra ts brs ra)) ∧
            ∀a, (a = ra → t a = t₁ a) ∧ (a = (renamePairFunc ra ts brs) ra → t a = t₂ a) ∧ (a ≠ ra → a ≠ (renamePairFunc ra ts brs) ra → ¬(t a).Dom)
      } := by
        simp_all only [combinePair, RA.Query.evaluateT, selectionT, joinT, projectionT,
          Finset.mem_singleton, Set.mem_setOf_eq, joinSingleT, PFun.mem_dom, forall_exists_index,
          Set.mem_union, not_or, not_exists, ne_eq]
        ext t
        apply Iff.intro
        · intro h
          obtain ⟨h, ht⟩ := h
          obtain ⟨t', h⟩ := h
          obtain ⟨hl, hr⟩ := h
          obtain ⟨t₂, hl⟩ := hl
          obtain ⟨ht₂, ht' ⟩ := hl
          obtain ⟨t₁, hr⟩ := hr
          obtain ⟨hr, htj⟩ := hr
          obtain ⟨t₃, hr⟩ := hr
          obtain ⟨ht₃, htr⟩ := hr

          simp_all only [Set.mem_setOf_eq, not_false_eq_true, Part.notMem_none, implies_true,
            Part.not_none_dom, and_true]

          have t₂Dom := RA.Query.evaluate.validSchema (renamePair ra ts brs) renamePair.isWellTyped_def t₂ ht₂
          rw [renamePair.schema_def] at t₂Dom

          have t₃Dom := (dbi.relations rn).validSchema t₃ ht₃
          rw [DatabaseInstance.validSchema] at t₃Dom

          have ⟨v₂, hv₂⟩ : ∃v, v ∈ t₂ (renamePairFunc ra ts brs ra) := by
            simp_rw [← PFun.mem_dom, t₂Dom, Finset.coe_image,
              Set.mem_image, Finset.mem_coe]
            use ra

          have ⟨v₃, hv₃⟩ : ∃v, v ∈ t₃ ra := by rw [← PFun.mem_dom, t₃Dom]; exact hra

          have t₁Dom : t₁.Dom = {ra} := by
            simp [Set.ext_iff]
            intro x
            simp_all only [Finset.coe_image]
            apply Iff.intro
            · intro a
              obtain ⟨w, h⟩ := a
              by_contra hc
              have := (htr x).2 hc
              simp_all only [not_false_eq_true, Part.notMem_none]
            · intro a
              subst a
              simp_all only
              use v₃

          have ⟨v₁, hv₁⟩ : ∃v, v ∈ t₁ ra := by rw [← PFun.mem_dom, t₁Dom, Set.mem_singleton_iff]

          use t₃
          simp [*]
          use t₂
          apply And.intro
          · rw [renamePair.evalT_def] at ht₂
            exact ht₂
          · intro a
            apply And.intro
            · intro a_1
              subst a_1
              rw [← (htr a).1 rfl, ← (htj a).2.1 v₁ hv₁, ht]
            . intro a_1
              subst a_1
              rw [← ht]
              simp [renamePair.evalT_def] at ht₂
              by_cases renamePairFunc ra ts brs ra = ra
              next heq =>
                rw [← (ht' ra).1 heq.symm]
                rw [ht, heq]
                rw [← (htj ra).1 v₂ ?_]
                . simp_all only [Finset.coe_image]
              next neq =>
                rw [ht, ← (ht' (renamePairFunc ra ts brs ra)).1 rfl, ← (htj (renamePairFunc ra ts brs ra)).1 v₂ ?_]
                . simp_all only [Finset.coe_image]

        · intro a
          simp_all only [Set.mem_setOf_eq]
          obtain ⟨t₁, h⟩ := a
          obtain ⟨ht₁, h⟩ := h
          obtain ⟨t₂, h⟩ := h
          obtain ⟨ht₂, hts, htj⟩ := h

          have ht₂' : t₂ ∈ RA.Query.evaluateT dbi (renamePair ra ts brs) := by simp [renamePair.evalT_def, ht₂]

          have t₂Dom := RA.Query.evaluate.validSchema (renamePair ra ts brs) renamePair.isWellTyped_def t₂ ht₂'
          rw [renamePair.schema_def] at t₂Dom

          have t₁Dom := (dbi.relations rn).validSchema t₁ ht₁
          rw [DatabaseInstance.validSchema] at t₁Dom

          haveI := fun a ↦ decidable_dom t₁Dom a
          haveI := fun a ↦ decidable_dom t₂Dom a

          apply And.intro ?_ hts
          . use λ a => ite (a = renamePairFunc ra ts brs ra) (t (renamePairFunc ra ts brs ra)) .none
            apply And.intro
            . use t₂
              simp_all
            . use λ a => ite (a = ra) (t ra) .none
              apply And.intro
              . use t₁
                simp_all
              . intro a
                apply And.intro
                . intro x h
                  simp_all only [Finset.coe_image]
                  split
                  next h_1 =>
                    subst h_1
                    simp_all only [↓reduceIte]
                  next h_1 => simp_all only [↓reduceIte, Part.notMem_none]
                . apply And.intro
                  . intro x h
                    simp_all only [Finset.coe_image]
                    split
                    next h_1 =>
                      subst h_1
                      simp_all only [↓reduceIte]
                    next h_1 => simp_all only [↓reduceIte, Part.notMem_none]
                  . intro ⟨h₁, h₂⟩
                    simp [Part.eq_none_iff]
                    intro v
                    by_cases hc₁ : a = ra
                    . subst hc₁
                      simp at h₂
                      exact h₂ v
                    . by_cases hc₂ : a = renamePairFunc ra ts brs ra
                      . subst hc₂
                        simp at h₁
                        exact h₁ v
                      . simp [Part.dom_iff_mem] at htj
                        apply (htj a).2.2 hc₁ hc₂


noncomputable def relJoins (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  ras.foldr (λ ra sq => .j (combinePair ra ts brs) sq) (.p ∅ (.R rn))

theorem relJoins.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ras.toFinset ⊆ dbs rn) :
  (relJoins ras ts brs).schema dbs = (ras.toFinset.image (λ ra => renamePairFunc ra ts brs ra)) ∪ ras.toFinset := by
    simp [relJoins]
    induction ras with
    | nil => simp_all
    | cons hd tl ih =>
      have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
      simp_all only [forall_const, List.toFinset_cons, List.foldr_cons, RA.Query.schema.eq_4,
        RA.Query.schema, Finset.insert_union, Finset.singleton_union, Finset.image_insert,
        Finset.union_insert, combinePair.schema_def]

theorem relJoins.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relJoins ras ts brs) := by
      simp [relJoins]
      induction ras with
      | nil => simp
      | cons hd tl ih =>
        have hhd : hd ∈ dbs rn := by simp at h; grind
        have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
        simp only [List.foldr_cons, RA.Query.isWellTyped.eq_4, RA.Query.isWellTyped,
          combinePair.isWellTyped_def hhd, true_and]
        apply ih htl

set_option maxHeartbeats 2000000

theorem relJoins.evalT_def [Fintype (adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h' : ras.toFinset ⊆ dbi.schema rn) :
    RA.Query.evaluateT dbi (relJoins ras ts brs) =
    {t |
      (∃t', t' ∈ (dbi.relations rn).tuples) ∧
      (∀ra ∈ ras.toFinset,
        ∃t' ∈ (dbi.relations rn).tuples,
          (t' ra = t (renamePairFunc ra ts brs ra)))
      ∧ (∀ra, ra ∉ ras.toFinset → t ra = .none)
    } := by
      induction ras with
      | nil =>
        simp only [relJoins, List.foldr_nil, RA.Query.evaluateT, projectionT, Finset.notMem_empty,
          IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and, exists_and_right,
          List.toFinset_nil]
      | cons hd tl ih =>
        simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, forall_eq_or_imp, not_or, and_imp]
        rw [relJoins]
        rw [List.foldr_cons]
        rw [← relJoins]
        simp
        rw [ih (by simp_all; grind)]
        ext t

        have hhd : hd ∈ dbi.schema rn := by simp at h'; grind

        simp [combinePair.evalT_def hhd]

        apply Iff.intro
        . intro ⟨t', ⟨t₁, ht₁⟩, t₂, ⟨⟨⟨t₃, ht₃⟩, ht₃'⟩, ht₂'⟩⟩
          apply And.intro
          . use t₃
          . apply And.intro
            . apply And.intro
              . sorry
              . intro ra hra
                have ⟨t₄, ht₄, ht₄'⟩ := ht₃'.1 ra hra
                use t₄
                apply And.intro ht₄
                simp_all
                sorry
            . sorry
        . sorry

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def relToRA (rn : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (rs brs : Finset String) : RA.Query String String :=
    .p (rs) ((relJoins (RelationSchema.ordering (dbs rn)) ts brs).j (adom dbs rs))

theorem relToRA.schema_def : (relToRA dbs rn ts rs brs).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA dbs rn ts rs brs) := by
    simp [relToRA, relJoins.isWellTyped_def, adom.isWellTyped_def, adom.schema_def]

theorem relToRA.evalT_def [Nonempty (adomRs dbi.schema)] [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hrs : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) :
    RA.Query.evaluateT dbi (relToRA dbi.schema rn ts rs brs) =
    {t | ∃h, RealizeDomSet (μ := μ) (Relations.boundedFormula (relations.R rn) ts) rs brs t h} := by
      simp_rw [RealizeDomSet, BoundedFormula.realize_rel]
      rw [← fol.Rel]
      simp_rw [folStruc_apply_RelMap, ArityToTuple.def_dite]
      simp only [relToRA, RA.Query.evaluateT, projectionT, joinT, joinSingleT,
        PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp,
        Set.mem_setOf_eq, exists_and_right]

      rw [relJoins.evalT_def (subset_of_eq (RelationSchema.ordering_eq_toFinset (dbi.schema rn)))]
      ext t
      rename_i inst inst_1 inst_2 inst_3
      simp_all only [nonempty_subtype, RelationSchema.ordering_eq_toFinset, Set.mem_setOf_eq, adom.complete_def,
        Finset.coe_inj]
      obtain ⟨w, h⟩ := inst
      apply Iff.intro
      · intro a
        obtain ⟨w_1, h_1⟩ := a
        obtain ⟨left, right⟩ := h_1
        obtain ⟨w_2, h_1⟩ := left
        obtain ⟨left, right_1⟩ := h_1
        obtain ⟨left, right_2⟩ := left
        obtain ⟨w_3, h_1⟩ := right_1
        obtain ⟨w_4, h_2⟩ := left
        obtain ⟨left, right_1⟩ := right_2
        obtain ⟨left_1, right_2⟩ := h_1
        obtain ⟨left_1, right_3⟩ := left_1
        obtain ⟨w_5, h_1⟩ := left_1
        obtain ⟨left_1, right_3⟩ := right_3
        obtain ⟨left_2, right_4⟩ := h_1
        obtain ⟨w_6, h_1⟩ := right_4
        apply And.intro
        · sorry
        · sorry
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w_1, h_1⟩ := left

        sorry
      -- ext t
      -- rw [relJoins.evalT_def (subset_of_eq (RelationSchema.ordering_eq_toFinset (dbi.schema rn)))]
      -- simp_all only [Set.mem_setOf_eq]
      -- simp_all only [RealizeDomSet, BoundedFormula.realize_rel, RelationSchema.ordering_mem, RelationSchema.ordering_eq_toFinset,
      --   Finset.coe_union, Finset.coe_image, exists_and_right]

      -- apply Iff.intro
      -- · intro a
      --   obtain ⟨w, h_1⟩ := a
      --   obtain ⟨left, right⟩ := h_1
      --   obtain ⟨w_1, h_1⟩ := left
      --   obtain ⟨left, right_1⟩ := h_1
      --   obtain ⟨left, right_2⟩ := left
      --   obtain ⟨w_2, h_1⟩ := right_1
      --   obtain ⟨w_3, h_2⟩ := left
      --   obtain ⟨left, right_1⟩ := w_3
      --   obtain ⟨left_1, right_2⟩ := h_1
      --   apply And.intro
      --   · apply Exists.intro
      --     . rw [← fol.Rel, folStruc_apply_RelMap] at right_1
      --       apply (congr_arg (λ x => x ∈ (dbi.relations rn).tuples) ?_).mp right_1
      --       . intro left right_1
      --         ext x
      --         simp_all only [PFun.mem_dom, Finset.mem_coe]
      --         apply Iff.intro
      --         · intro a
      --           obtain ⟨w_4, h_1⟩ := a
      --           by_contra hc
      --           rw [(right x).2 hc] at h_1
      --           simp_all
      --         · intro a
      --           simp_all only
      --           have w_2_Dom := RA.Query.evaluate.validSchema (adom dbi.schema rs) adom.isWellTyped_def w_2 left
      --           rw [adom.schema_def] at w_2_Dom
      --           rw [← Finset.mem_coe, ← w_2_Dom, PFun.mem_dom] at a
      --           obtain ⟨v, hv⟩ := a
      --           rw [(right_1 x).2.1 v hv]
      --           use v
      --       . funext x
      --         simp_all only [ArityToTuple.def_dite]
      --         by_cases hc : x ∈ dbi.schema rn
      --         . simp_all only [↓reduceDIte, Part.some_inj]
      --           have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index hc))
      --           simp [hk]
      --           cases k
      --           next val =>
      --             have in_rs : val ∈ rs := by
      --               apply h
      --               simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      --               apply Or.inl
      --               use RelationSchema.index hc
      --               simp [hk]
      --             have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 val := by
      --               rw [← PFun.mem_dom, left]
      --               simp [renamePairFunc]
      --               apply Or.inr
      --               use x
      --               simp [hc, renameFunc, hk, TermtoAtt]
      --             simp
      --             congr
      --             rw [(right val).1 in_rs]
      --             rw [(right_2 val).1 v in_w_1]
      --           next val =>
      --             have in_rs : (FreeMap n brs val) ∈ rs := by
      --               apply h
      --               simp_all only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, FRan.mem_def, or_true]
      --             have ⟨v, in_w_1⟩ : ∃v, v ∈ w_1 (FreeMap n brs val) := by
      --               rw [← PFun.mem_dom, left]
      --               simp [renamePairFunc]
      --               apply Or.inr
      --               use x
      --               simp [hc, renameFunc, hk, TermtoAtt]
      --             simp
      --             congr
      --             rw [(right (FreeMap n brs val)).1 in_rs]
      --             rw [(right_2 (FreeMap n brs val)).1 v in_w_1]
      --         . simp_all only [↓reduceDIte]
      --   · simp at left_1
      --     have : t.ran ⊆ w_2.ran := by
      --       simp [PFun.ran]
      --       intro v x hv
      --       have in_rs : x ∈ rs := by
      --         by_contra hc
      --         have := (right x).2 hc
      --         simp_all
      --       have ⟨v', in_w_2⟩ : ∃v, v ∈ w_2 x := by
      --         rw [← PFun.mem_dom, left_1.1]
      --         exact in_rs
      --       use x
      --       rw [← (right_2 x).2.1 v' in_w_2, ← (right x).1 in_rs]
      --       exact hv
      --     rw [@Set.subset_def]
      --     apply λ a ha => left_1.2 (this ha)
      -- · intro a
      --   obtain ⟨left, right⟩ := a
      --   obtain ⟨w, h_1⟩ := left
      --   sorry

noncomputable def toRA
  (f : (fol dbs).BoundedFormula String n) (rs brs : Finset String) (hn : n + depth f < brs.card) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt brs t₁) (TermtoAtt brs t₂) (adom dbs rs)
    | .rel (.R rn) ts => relToRA dbs rn ts rs brs
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ rs brs (by simp_all; grind)) (toRA f₂ rs brs (by simp_all; grind)))
    | .all sf => (adom dbs rs).d (.p rs ((adom dbs (rs ∪ FRan (FreeMap (n + 1) brs))).d (toRA sf (rs ∪ FRan (FreeMap (n + 1) brs)) brs (by simp_all; grind))))

theorem toRA.schema_def :
    (toRA dbs φ rs brs hn).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n rn => simp [toRA, relToRA.schema_def]
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsAtomic) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q rs brs hn).isWellTyped dbs := by
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
  (hq : q.IsQF) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card):
    (toRA dbs q rs brs hn).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h' hn
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp only [RA.Query.isWellTyped, RA.Query.schema]
        simp at h'
        have : q₁.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := by grind
        have : q₂.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]

theorem toRA.isWellTyped_def_IsPrenex {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsPrenex) (h' : q.freeVarFinset ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (hn : n + depth q < brs.card)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q (rs ∪ FRan (FreeMap n brs)) brs hn).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf (by grind) (by grind)
      | all =>
        simp [toRA]
        simp at hn
        rename_i inst_1 n_1 φ h_1 h_ih

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by rw [FreeMap.FRan_union_add_one (by grind)]

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        exact Finset.union_subset_union_right (FreeMap.FRan_sub_add_one (by grind))

      | ex =>
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp at h' h'' hn

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by rw [FreeMap.FRan_union_add_one (by grind)]

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        exact Finset.union_subset_union_right (FreeMap.FRan_sub_add_one (by grind))

theorem toRA.falsum_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] :
    (toRA dbi.schema (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs t h} := by
        have : (RA.Query.evaluateT dbi (adom dbi.schema rs)).diff (RA.Query.evaluateT dbi (adom dbi.schema rs)) = ∅ := Set.diff_self
        simp_rw [toRA, RA.Query.evaluateT, diffT, this]
        simp [RealizeDomSet, BoundedFormula.Realize]

theorem toRA.term_equal_def [Nonempty μ] [folStruc dbi (μ := μ)] {t₁ t₂ : (fol dbi.schema).Term (String ⊕ Fin n)} {t : String →. μ} {rs : Finset String}
  (h : t.Dom = ↑rs) (h' : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs):
    t (TermtoAtt brs t₁) = t (TermtoAtt brs t₂) ↔
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
  (h : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs) (hn : n + depth (t₁ =' t₂) < brs.card) :
    (toRA dbi.schema (t₁ =' t₂) rs brs hn).evaluateT dbi = {t | ∃h, RealizeDomSet (t₁ =' t₂) rs brs t h} := by
      simp_rw [Term.bdEqual, toRA, RA.Query.evaluateT, selectionT]
      simp_rw [RealizeDomSet]

      rw [adom.complete_def]
      ext t
      simp_rw [Set.mem_setOf_eq, exists_and_right]

      apply Iff.intro
      . intro ⟨⟨w_1, h_2, h_3⟩, right⟩
        split_ands
        . use h_2
          apply (term_equal_def h_2 h).mp right
        . apply h_3
      . intro ⟨⟨w_1, h_2⟩, right⟩
        apply And.intro
        . apply And.intro ?_ (And.intro w_1 right)
          have ⟨v, hv⟩ : ∃v, v ∈ t.ran := by
            rw [Finset.subset_iff] at h
            simp [PFun.ran, exists_comm, ← PFun.mem_dom, w_1]
            have ⟨k, hk⟩ := Term.cases t₁
            cases k with
            | inl val =>
              use val
              apply h
              simp [hk, Term.bdEqual]
            | inr i =>
              cases n with
              | zero => apply Fin.elim0 i
              | succ n' =>
                use FreeMap (n' + 1) brs (Fin.last n')
                apply h
                simp
          simp [DatabaseInstance.domain, Set.subset_def] at right
          obtain ⟨rn, att, t, ht₁, ht₂⟩ := right v hv
          use rn
          simp [adomRs]
          apply And.intro
          . simp_rw [← dbi.validSchema, Finset.eq_empty_iff_forall_notMem, ← Finset.mem_coe,  ← (dbi.relations rn).validSchema t ht₁]
            simp_rw [PFun.mem_dom, not_exists, not_forall, not_not]
            use att, v
            exact Part.eq_some_iff.mp ht₂
          . use t
        . exact ((term_equal_def w_1 h).mpr h_2)

theorem toRA.imp_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)]
  (hμ : ∀v : μ, v ∈ dbi.domain) (hn : n + depth (q₁ ⟹ q₂) < brs.card)
  (ih₁ : (toRA dbi.schema q₁ rs brs (by simp at hn; grind)).evaluateT dbi = {t | ∃h, RealizeDomSet q₁ rs brs t h})
  (ih₂ : (toRA dbi.schema q₂ rs brs (by simp at hn; grind)).evaluateT dbi = {t | ∃h, RealizeDomSet q₂ rs brs t h}) :
    (toRA dbi.schema (q₁.imp q₂) rs brs hn).evaluateT dbi = {t | ∃h, RealizeDomSet (q₁.imp q₂) rs brs t h} := by
      ext t
      simp only [toRA, RA.Query.evaluateT.eq_7, diffT, Set.diff, adom.complete_def,
        Set.mem_setOf_eq, RA.Query.evaluateT, not_and, not_not, RealizeDomSet,
        BoundedFormula.realize_imp, exists_and_right]
      simp_all only [nonempty_subtype, RealizeDomSet, Finset.coe_inj, exists_and_right,
        Set.mem_setOf_eq, and_true, and_imp, forall_exists_index, exists_true_left,
        TupleToFun.tuple_eq_self]
      apply Iff.intro
      · intro a_1
        simp_all only [Finset.coe_inj, TupleToFun.tuple_eq_self, implies_true, exists_const, and_self]
      · intro ⟨⟨w_1, h_1⟩, right⟩
        simp_all [Finset.coe_inj, TupleToFun.tuple_eq_self, implies_true, and_self]
        apply adom.exists_tuple_from_value hμ

theorem toRA.not_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [Fintype ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)]
  (hμ : ∀v : μ, v ∈ dbi.domain) (hn : n + depth (∼q) < brs.card)
  (ih : (toRA dbi.schema q rs brs (by simp at hn; grind)).evaluateT dbi = {t | ∃h, RealizeDomSet q rs brs t h}) :
    (toRA dbi.schema q.not rs brs hn).evaluateT dbi = {t | ∃h, RealizeDomSet (q.not) rs brs t h} := by
      exact imp_def hμ hn ih falsum_def

theorem toRA.all_def [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] {q : (fol dbi.schema).BoundedFormula String (n + 1)}
  (hμ : ∀v : μ, v ∈ dbi.domain) (hn : n + depth (∀'q) < brs.card) (h : (FreeMap (n + 1) brs) (Fin.last n) ∉ q.freeVarFinset)
  (ih : (toRA dbi.schema q (q.freeVarFinset ∪ FRan (FreeMap (n + 1) brs)) brs (by simp at hn; grind)).evaluateT dbi = {t | ∃h, RealizeDomSet q (q.freeVarFinset ∪ FRan (FreeMap (n + 1) brs)) brs t h}) :
    (toRA dbi.schema q.all (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs hn).evaluateT dbi = {t | ∃h, RealizeDomSet (q.all) (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs t h} := by
      simp only [toRA, RA.Query.evaluateT, Finset.union_assoc, diffT, Set.diff]
      rw [FreeMap.FRan_union_add_one (by grind), ih]

      ext t

      simp_all only [RealizeDomSet, exists_and_right, adom.complete_def,
        exists_prop, Set.mem_setOf_eq, not_and, forall_exists_index, projectionT, not_exists, not_forall,
        and_imp, not_true_eq_false, imp_false, forall_true_left, forall_and_index, BoundedFormula.realize_all,
        Nat.succ_eq_add_one]

      apply Iff.intro
      · intro a
        simp_all only [Finset.coe_union, Finset.mem_union, not_or, exists_true_left, and_true]
        intro a_1
        obtain ⟨left, right⟩ := a
        obtain ⟨⟨rn, hrn, t', ht'⟩, left, right_1⟩ := left

        rw [← Finset.coe_union] at left

        let t'' := λ a => ite (a ∈ q.freeVarFinset ∪ FRan (FreeMap n brs)) (t a) (ite (a = FreeMap (n + 1) brs (Fin.last n)) (a_1) (Part.none))

        by_contra hc

        have ⟨rn'', hrn'', t_, ht_⟩ : ∃ rn ∈ adomRs dbi.schema, ∃ t', t' ∈ (dbi.relations rn).tuples := by
          apply adom.exists_tuple_from_value hμ

        have := right t'' rn'' hrn'' t_ ht_ ?_ ?_ ?_
        . rw [← not_forall_not] at this
          apply this
          simp [t'']
          intro x
          apply And.intro
          . intro h₁ h₂ h₃
            cases h₁
            . simp_all
            . simp_all
          . intro h₁ h₂
            rw [@Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, left]
            simp [h₁, h₂]
        . ext x
          simp [t'']
          split
          next h_2 =>
            cases h_2 with
            | inl h_3 => simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
            | inr h_4 =>
              simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
              exact Or.inr (by apply FreeMap.FRan_sub_add_one (by simp at hn; grind) h_4)
          next h_2 =>
            split
            next h_3 =>
              subst h_3
              simp_all only [Part.some_dom, false_or, FRan.mem_def, or_true]
            next h_3 =>
              simp_all [not_or, Part.not_none_dom]
              by_contra hc'
              rw [FreeMap.mem_FRan_add_one_cases (by grind)] at hc'
              simp_all
        . simp [PFun.ran, t'', Set.subset_def]
          intro v a hv
          split at hv
          . apply right_1
            simp [PFun.ran]
            use a
          . split at hv
            . simp [hμ]
            . simp at hv

        . by_contra hc'
          apply hc
          apply (BoundedFormula.Realize.equiv (fun i ↦ ?_) ?_).mp hc'
          . intro a ha
            refine TupleToFun.tuple_eq_att_ext ?_
            simp [t'']
            intro h _
            exact False.elim (h ha)
          . induction i using Fin.lastCases with
            | cast j =>
              have : FreeMap (n + 1) brs j.castSucc ∈ FRan (FreeMap n brs) := by exact FRan.mem_def
              simp only [Fin.snoc_castSucc, Function.comp_apply]
              simp [TupleToFun, t'']
              congr
              simp [this]
              rw [@FreeMap.add_one_def]
            | last =>
              simp [t'']
              have : FreeMap (n + 1) brs (Fin.last n) ∉ q.freeVarFinset ∪ FRan (FreeMap n brs) := by
                exact Finset.notMem_union.mpr (And.intro h (FRan.notMem_FreeMap_lift (by grind)))

              simp [this]

      · intro ⟨⟨w_1, h_1⟩, right⟩
        simp_all only [and_self, and_true]

        apply And.intro
        . exact adom.exists_tuple_from_value hμ
        . intro x rn hrn t' ht' hp hq a

          by_contra hc
          simp at hc

          apply a

          apply (BoundedFormula.Realize.equiv (fun i ↦ ?_) ?_).mp (h_1 ((TupleToFun hp) (FreeMap (n + 1) brs (Fin.last n))))
          . intro a ha
            exact TupleToFun.tuple_eq_att_ext ((hc a).1 (Or.inl ha))
          . induction i using Fin.lastCases with
            | cast j =>
              simp only [Fin.snoc_castSucc, Function.comp_apply]
              simp [TupleToFun]
              have := (hc (FreeMap n brs j)).1 (by simp)
              congr
            | last => simp


theorem toRA.evalT_def_IsAtomic [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card) :
    (toRA dbi.schema q rs brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | equal t₁ t₂ => exact equal_def h hn
      | rel R ts =>
        cases R with
        | R rn => exact relToRA.evalT_def h


theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hμ : ∀v, v ∈ dbi.domain) (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card) :
    (toRA dbi.schema q rs brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | falsum => exact falsum_def
      | of_isAtomic h_at => exact toRA.evalT_def_IsAtomic h_at h hn

      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h

        exact toRA.imp_def hμ hn (ih₁ (Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩) (by simp at hn; grind)) (ih₂ (Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩) (by simp at hn; grind))


theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n} [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)]
  (hμ : ∀v, v ∈ dbi.domain) (hq : q.IsPrenex) (h' : brs ∩ q.freeVarFinset = ∅) (hn : n + depth q < brs.card) :
    (toRA dbi.schema q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs t h} := by
        induction hq with
        | of_isQF hqf => exact evalT_def_IsQF hμ hqf (fun ⦃a⦄ a ↦ a) (by grind)

        | all hφ ih =>
          apply all_def hμ (by grind) ?_

          . simp [← Nat.add_assoc] at hn

            exact ih h' hn

          . simp [Finset.eq_empty_iff_forall_notMem] at h'
            apply h'
            rw [FreeMap.fromIndex_brs_def]
            . simp
            . grind

        | ex hφ ih =>
          rename_i n' φ

          simp_rw [BoundedFormula.ex]
          apply not_def hμ
          have helper {n} : ∀ψ : (fol dbi.schema).BoundedFormula String n, (∼ψ).freeVarFinset = ψ.freeVarFinset := by simp
          rw [helper (φ.not.all)]

          apply all_def hμ (by simp at hn ⊢; grind) ?_ ∘ not_def hμ (by simp at hn ⊢; grind)

          . rw [helper φ]
            simp_rw [BoundedFormula.freeVarFinset, Finset.union_empty] at h' ⊢
            simp [← Nat.add_assoc] at hn

            exact ih h' hn

          . simp [Finset.eq_empty_iff_forall_notMem] at h'
            simp
            apply h'
            rw [FreeMap.fromIndex_brs_def]
            . simp
            . grind



-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs (toPrenex q) q.schema (FreshAtts (toPrenex q)) (by
    have ⟨k, hk⟩ := FreshAtts.card_def (toPrenex q)
    rw [hk]
    grind only
  )

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toRA.schema_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan (FreeMap 0 (FreshAtts (toPrenex q))) = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp [FRan, FRanS]
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, ← this]
    apply toRA.isWellTyped_def_IsPrenex ?_ ?_ ?_ ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp
    . simp
    . have ⟨k, hk⟩ := FreshAtts.card_def (toPrenex q)
      rw [hk]
      grind only

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] [Nonempty μ] (q : FOL.Query dbi.schema) (hμ : ∀v, v ∈ dbi.domain) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q ∩ {t | t.ran ⊆ dbi.domain} := by
    rw [FOL.Query.evaluateT, Set.ext_iff]
    intro t
    rw [@Set.mem_inter_iff]
    rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
    rw [fol_to_ra_query, BoundedQuery.schema]
    simp_rw [toPrenex]

    have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
    have helper : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan (FreeMap 0 (FreshAtts (BoundedQuery.toFormula q).toPrenex))
      = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp [FRan, FRanS]
    rw [← freeVarFinset_toPrenex, ← helper, toRA.evalT_def_IsPrenex hμ hq]

    rw [Set.mem_setOf_eq]
    simp only [BoundedFormula.realize_toPrenex, RealizeDomSet]
    simp_all only [freeVarFinset_toPrenex]

    have : ∀t' : String → μ, (t' ∘ (FreeMap 0 (FreshAtts (BoundedQuery.toFormula q).toPrenex))) = (default : Fin 0 → μ) := by intro t'; ext v; exact False.elim (Fin.elim0 v)
    simp_rw [this]
    . simp
    . simp
