import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.FreshAtts
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.RA.EquivRules

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


noncomputable def renamer {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (undefined ra : String) : String :=
  ((RelationSchema.index? (dbs rn) ra).map (TermtoAtt brs ∘ ts)).getD (undefined)

theorem renamer.notMem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∉ dbs rn) :
  renamer ts brs u ra = u := by
    rw [renamer, RelationSchema.index?_none.mpr h, Option.map_none, Option.getD_none]

theorem renamer.mem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  renamer ts brs u ra = (TermtoAtt brs ∘ ts) (RelationSchema.index h) := by
    have ⟨k, hk⟩ := RelationSchema.index?_isSome_eq_iff.mp (RelationSchema.index?_isSome.mpr h)
    rw [RelationSchema.index]
    simp_rw [renamer, hk, Option.map_some, Option.getD_some, Option.get]

noncomputable def getRAs (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u a : String) : Finset String :=
  (dbs rn).filter (λ ra => renamer ts brs u ra = a)

theorem getRAs.mem_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {u a : String} :
  ra ∈ getRAs ts brs u a ↔ ra ∈ dbs rn ∧ renamer ts brs u ra = a := by simp [getRAs]

noncomputable instance {dbs} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} : Fintype ↑{ra | ra ∈ dbs rn ∧ renamer ts brs u ra = a} := by
  apply Fintype.ofFinset (getRAs ts brs u a)
  intro ra
  simp [Set.mem_setOf_eq.mp getRAs.mem_def]

theorem getRAs.def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {a : String} :
  getRAs ts brs u a = {ra | ra ∈ dbs rn ∧ renamer ts brs u ra = a} := by simp [getRAs]

theorem getRAs.renamer_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) (h : getRAs ts brs u a ≠ ∅) :
  (getRAs ts brs u a).image (λ ra => renamer ts brs u ra) = {a} := by
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

noncomputable def renamePairFunc (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : String → String :=
  renameFunc ra (renamer ts brs u ra)

-- noncomputable def renamePairTuple (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : (String →. μ) → String →. μ :=
--   λ t => λ a => ite (renamer ts brs ra = a) (t ra) (ite (ra = a) (.none) (t a))

-- theorem renamePairTuple.eq_comp_def {t : String →. μ} (h : ¬(renamer ts brs ra) ∈ t.Dom): t ∘ renamePairFunc ra ts brs = renamePairTuple ra ts brs t := by
--   ext a v
--   simp [renamePairFunc, renamePairTuple, renameFunc]
--   by_cases h₁ : a = renamer ts brs ra
--   . subst h₁; simp only [↓reduceIte]
--   . by_cases h₂ : a = ra
--     . subst h₂
--       simp_rw [h₁, ne_comm.mp h₁, reduceIte, Part.notMem_none]
--       simp_all only [PFun.mem_dom, not_exists]
--     . simp_rw [h₁, ne_comm.mp h₁, h₂, ne_comm.mp h₂, reduceIte]

theorem getRAs.renamePair_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) (h : getRAs ts brs u a ≠ ∅) :
  (getRAs ts brs u a).image (λ ra => renamePairFunc ra ts brs u ra) = {a} := by
    simp_rw [renamePairFunc, renameFunc.old_def]
    exact renamer_def ts brs a h

theorem getRAs.biUnion_renamePairFunc_def (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) :
  Finset.biUnion ((dbs rn).image (λ ra => renamePairFunc ra ts brs u ra)) (λ a => (getRAs ts brs u a)) = dbs rn := by
    ext a'
    simp_all only [Finset.mem_biUnion, Finset.mem_image, mem_def, exists_eq_right_right',
      and_iff_right_iff_imp]
    intro ha'
    use a'
    apply And.intro ha' renameFunc.old_def

noncomputable def renamePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
  .r (renamePairFunc ra ts brs u) (.R rn)

theorem renamePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (renamePair ra ts brs u).schema dbs = (dbs rn).image (renamePairFunc ra ts brs u) := rfl

theorem renamePair.schema_update_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) (h' : renamer ts brs u ra ∉ dbs rn) :
  (renamePair ra ts brs u).schema dbs = (insert (renamer ts brs u ra) (dbs rn)).erase ra  := by
    simp [renamePair.schema_def, renamePairFunc, Finset.ext_iff, renameFunc]
    intro a
    apply Iff.intro
    . intro ⟨a', ha', h₁⟩
      split_ifs at h₁ with h₂ h₃
      . subst h₂ h₁
        simp_all only [not_true_eq_false]
      . subst h₃ h₁
        apply And.intro
        . exact h₂ ∘ Eq.symm
        . exact Or.inl rfl
      . simp_all only [not_false_eq_true, or_true, and_self]
    . intro ⟨h₁, h₂⟩
      cases h₂ with
      | inl h₃ =>
        use ra
        simp [← h₃, h]
      | inr h₃ =>
        use a
        apply And.intro h₃
        simp_rw [h₁, reduceIte, ite_eq_right_iff]
        intro h₄
        subst h₄
        exact False.elim (h' h₃)

theorem renamePair.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
    RA.Query.isWellTyped dbs (renamePair ra ts brs u) := by
      simp [renamePair, renamePairFunc, rename_func_bijective]

theorem renamePair.evalT_def {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
    RA.Query.evaluateT dbi (renamePair ra ts brs u) =
      {t | t ∘ (renamePairFunc ra ts brs u) ∈ (dbi.relations rn).tuples} := by
        simp [renamePair]
        rfl

-- theorem renamePair.evalT_update_def [Fintype (adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
--   (h : ra ∈ dbi.schema rn) (h' : renamer ts brs ra ∉ dbi.schema rn) :
--     RA.Query.evaluateT dbi (renamePair ra ts brs) =
--       (dbi.relations rn).tuples.image (λ t => t ∘ renamer ts brs) := by
--         simp [Set.ext_iff]
--         intro t
--         apply Iff.intro
--         · intro a
--           -- have := t.Dom ...
--           use t ∘ renamePairFunc ra ts brs
--           simp [renamePair.evalT_def] at a
--           simp_all [renamePairFunc]
--           apply And.intro a
--           . ext a v
--             simp [renameFunc]
--             split_ifs with h₁ h₂
--             . rw [renamer.mem_def h] at h₁
--               by_cases hc : a ∈ dbi.schema rn
--               . rw [renamer.mem_def hc] at h₁
--                 sorry
--               . rw [renamer.notMem_def hc] at h₁
--                 subst h₁
--                 aesop?
--             . subst h₂
--               sorry
--             . sorry
--         · intro a
--           obtain ⟨w, h⟩ := a
--           obtain ⟨left, right⟩ := h
--           subst right
--           rw [evalT_def]
--           apply Set.mem_setOf.mpr
--           convert left
--           rw [renamePairTuple.eq_comp_def]
--           . sorry
--           . rw [Part.dom_iff_mem, renamePairTuple, if_pos rfl, ← PFun.mem_dom]
--             convert h
--             rw [(dbi.relations rn).validSchema _ left, DatabaseInstance.validSchema, Finset.mem_coe]
--             sorry


noncomputable def combinePair (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
  .j (renamePair ra ts brs u) (.R rn)

theorem combinePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  (combinePair ra ts brs u).schema dbs = dbs rn ∪ {renamePairFunc ra ts brs u ra} := by
    simp [combinePair, renamePair.schema_def]
    ext a
    simp_all only [Finset.mem_union, Finset.mem_image, Finset.mem_insert]
    apply Iff.intro
    · intro a_1
      cases a_1 with
      | inl h_1 =>
        obtain ⟨w, h_1⟩ := h_1
        obtain ⟨left, right⟩ := h_1
        subst right
        simp [renamePairFunc, renameFunc]
        split
        . split
          . apply Or.inl rfl
          . apply Or.inr h
        . split
          . simp_all
          . apply Or.inr left
      | inr h_2 => simp_all only [or_true]
    · intro a_1
      cases a_1 with
      | inl h_1 =>
        subst h_1
        apply Or.inl
        use ra
      | inr h_2 =>
        by_cases hc : ra = a
        . simp_all
        . apply Or.inr h_2

theorem combinePair.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
    RA.Query.isWellTyped dbs (combinePair ra ts brs u) := by
      simp [combinePair, renamePair.isWellTyped_def]

theorem combinePair.evalT_def {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
    RA.Query.evaluateT dbi (combinePair ra ts brs u) =
      {t : String →. μ | ∃t₁ ∈ (dbi.relations rn).tuples, ∃t₂, t₂ ∘ (renamePairFunc ra ts brs u) ∈ (dbi.relations rn).tuples ∧
            ∀a, (a ∈ t₁.Dom → t a = t₁ a) ∧ (a ∈ PFun.Dom t₂ → t a = t₂ a) ∧ (a ∉ t₁.Dom ∪ PFun.Dom t₂ → t a = .none)
      } := by
        simp_all only [combinePair, RA.Query.evaluateT, joinT, joinSingleT,
          Set.mem_union, not_or, and_imp]
        ext t
        apply Iff.intro
        · intro h
          obtain ⟨t₂, h⟩ := h
          obtain ⟨ht₂, h⟩ := h
          obtain ⟨t₁, h⟩ := h
          obtain ⟨ht₁, h⟩ := h

          simp_all only [PFun.mem_dom, forall_exists_index, not_exists, Set.mem_setOf_eq]

          use t₁
          simp [*]
          use t₂
          split_ands
          · rw [renamePair.evalT_def] at ht₂
            exact ht₂
          . intro a
            split_ands
            . intro v₁ hv₁
              rw [(h a).2.1 v₁ hv₁]

            . intro v₂ hv₂
              rw [(h a).1 v₂ hv₂]

            . intro h₁ h₂
              apply (h a).2.2 h₂ h₁

        · intro a
          simp_all only [Set.mem_setOf_eq]
          obtain ⟨t₁, h⟩ := a
          obtain ⟨ht₁, h⟩ := h
          obtain ⟨t₂, h⟩ := h
          obtain ⟨ht₂, htj⟩ := h

          have ht₂' : t₂ ∈ RA.Query.evaluateT dbi (renamePair ra ts brs u) := by simp [renamePair.evalT_def, ht₂]

          have t₂Dom := RA.Query.evaluate.validSchema (renamePair ra ts brs u) renamePair.isWellTyped_def t₂ ht₂'
          rw [renamePair.schema_def] at t₂Dom

          have t₁Dom := (dbi.relations rn).validSchema t₁ ht₁
          rw [DatabaseInstance.validSchema] at t₁Dom

          haveI : ∀a, Decidable (a ∈ PFun.Dom t₁) := fun a ↦ decidable_dom t₁Dom a
          haveI : ∀a, Decidable (a ∈ PFun.Dom t₂) := fun a ↦ decidable_dom t₂Dom a


          use λ a => ite (a ∈ PFun.Dom t₂) (t a) .none
          apply And.intro
          . convert ht₂' with _ _ a
            split_ifs with h'
            . rw [(htj a).2.1 h']
            . rw [Eq.comm, Part.eq_none_iff']
              exact h'
          . use λ a => ite (a ∈ t₁.Dom) (t a) .none
            apply And.intro
            . convert ht₁ with a
              split_ifs with h'
              . rw [(htj a).1 h']
              . rw [Eq.comm, Part.eq_none_iff']
                exact h'
            . intro a
              apply And.intro
              . intro h
                simp_all only [Finset.coe_image]
                split
                next h_1 =>
                  simp_all only [Finset.mem_coe, Set.mem_image, forall_exists_index, and_imp,
                    not_exists, not_and, PFun.dom_mk, Set.mem_setOf_eq]
                next h_1 => simp [h_1] at h
              . apply And.intro
                . intro h
                  simp_all only [Finset.coe_image]
                  split
                  next h_1 =>
                    simp_all only [Finset.mem_coe, Set.mem_image, forall_exists_index, and_imp,
                      not_exists, not_and, PFun.dom_mk, Set.mem_setOf_eq]
                  next h_1 =>
                    rw [PFun.dom_mk, Set.mem_setOf_eq, if_neg h_1] at h
                    exact False.elim h
                . intro h₂ h₁
                  simp [Part.eq_none_iff]
                  intro v
                  by_cases hc₁ : a ∈ t₁.Dom
                  . rw [PFun.mem_dom, if_pos hc₁, not_exists] at h₁
                    exact h₁ v

                  . by_cases hc₂ : a ∈ PFun.Dom t₂
                    . rw [PFun.mem_dom, if_pos hc₂, not_exists] at h₂
                      exact h₂ v
                    . have := (htj a).2.2 hc₁ hc₂
                      simp [this]


noncomputable def relJoins (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
  ras.foldr (λ ra sq => .j (combinePair ra ts brs u) sq) (.R rn)

theorem relJoins.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ras.toFinset ⊆ dbs rn) :
  (relJoins ras ts brs u).schema dbs = (ras.toFinset.image (λ ra => renamePairFunc ra ts brs u ra)) ∪ (dbs rn) := by
    simp [relJoins]
    induction ras with
    | nil => simp_all
    | cons hd tl ih =>
      have hhd : hd ∈ dbs rn := by simp at h; grind
      have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
      simp_all only [forall_const, List.toFinset_cons, List.foldr_cons, RA.Query.schema.eq_4,
        RA.Query.schema, Finset.insert_union, Finset.image_insert, combinePair.schema_def]
      simp_all only [Finset.union_singleton, Finset.insert_union]
      grind

theorem relJoins.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relJoins ras ts brs u) := by
      simp [relJoins]
      induction ras with
      | nil => simp
      | cons hd tl ih =>
        have hhd : hd ∈ dbs rn := by simp at h; grind
        have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
        simp only [List.foldr_cons, RA.Query.isWellTyped.eq_4, RA.Query.isWellTyped,
          combinePair.isWellTyped_def, true_and]
        apply ih htl

theorem test {dbi : DatabaseInstance String String μ} (t' : String →. μ) :
  t' ∘ renamePairFunc hd ts brs u ∈ (dbi.relations rn).tuples ↔ t' ∈ (dbi.relations rn).tuples.image (λ t => t ∘ renamePairFunc hd ts brs u) := by
    simp_all
    apply Iff.intro
    · intro a_1
      use t' ∘ renamePairFunc hd ts brs u
      apply And.intro a_1
      funext a
      simp [renamePairFunc, rename_func_cancel_self]
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      convert left
      funext
      simp [renamePairFunc, rename_func_cancel_self]

set_option maxHeartbeats 2000000

theorem relJoins.evalT_def {dbi : DatabaseInstance String String μ} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : ras.toFinset ⊆ dbi.schema rn) (h' : ras.toFinset.image (λ ra => renamer ts brs ra u) ∩ dbi.schema rn = ∅) :
    RA.Query.evaluateT dbi (relJoins ras ts brs u) =
    {t |
      (∃t', t' ∈ (dbi.relations rn).tuples ∧
        ∀ra, (ra ∈ dbi.schema rn → t ra = t' ra ∧ (∀a ∈ ras.toFinset.image (λ ra => renamer ts brs ra u), t a = t' (renamePairFunc ra ts brs a u)))
      ∧ (ra ∉ dbi.schema rn → ra ∉ (ras.toFinset.image (λ ra => renamer ts brs ra u)) → t ra = .none))
    } := by
      induction ras with
      | nil =>
        simp only [relJoins, List.foldr_nil, RA.Query.evaluateT, List.toFinset_nil,
          Finset.image_empty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
          not_false_eq_true, forall_const]
        ext t
        simp only [Set.mem_setOf_eq]
        apply Iff.intro
        . intro ht
          use t
          apply And.intro ht
          simp only [implies_true, true_and]
          intro ra hra
          rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema t ht, DatabaseInstance.validSchema]
          exact hra
        . intro ⟨t', ht', ht''⟩
          convert ht'
          refine PFun.ext' ?_ ?_
          . intro a
            rw [(dbi.relations rn).validSchema _ ht', DatabaseInstance.validSchema, Finset.mem_coe]
            apply Iff.intro
            · intro a_1
              by_contra hc
              simp [PFun.mem_dom, (ht'' a).2 hc] at a_1
            · intro a_1
              rw [PFun.mem_dom, (ht'' a).1 a_1, ← PFun.mem_dom]
              rw [(dbi.relations rn).validSchema _ ht', DatabaseInstance.validSchema, Finset.mem_coe]
              exact a_1
          . intro ra p q
            have : ra ∈ dbi.schema rn := by
              rw [(dbi.relations rn).validSchema _ ht', DatabaseInstance.validSchema] at q;
              exact q
            simp_rw [PFun.fn_apply, (ht'' ra).1 this]

      | cons hd tl ih =>
        simp only [List.toFinset_cons, Finset.image_insert, Finset.mem_insert, Finset.mem_image,
          List.mem_toFinset, not_or, not_exists, not_and, and_imp]
        rw [relJoins]
        rw [List.foldr_cons]
        rw [← relJoins]
        simp
        rw [ih (by simp_all; grind) (by simp_all; grind)]
        ext t

        have hhd : hd ∈ dbi.schema rn := by simp at h; grind

        simp [combinePair.evalT_def]

        apply Iff.intro
        . intro a
          simp_all only [Finset.mem_image, List.mem_toFinset, forall_exists_index, and_imp, not_exists, not_and,
            List.toFinset_cons]
          obtain ⟨w, h⟩ := a
          obtain ⟨left, right⟩ := h
          obtain ⟨w_1, h⟩ := left
          obtain ⟨w_2, h_1⟩ := right
          obtain ⟨left, right⟩ := h
          obtain ⟨left_1, right_1⟩ := h_1
          obtain ⟨w_3, h⟩ := right
          obtain ⟨w_4, h_1⟩ := left_1
          obtain ⟨left_1, right⟩ := h
          obtain ⟨left_2, right_2⟩ := h_1

          use w_4
          simp_all only [true_and]
          intro ra
          apply And.intro
          · intro h
            split_ands
            . have ⟨v, hv⟩ : ∃v, v ∈ w_4 ra := by rw [← PFun.mem_dom, (dbi.relations rn).validSchema _ left_2, DatabaseInstance.validSchema]; exact h
              have hv' := hv
              rw [← ((right_2 ra).1 h).1] at hv' ⊢
              rw [← (right_1 ra).2.1 v hv']
            . have ⟨v, hv⟩ : ∃v, v ∈ w_4 ra := by rw [← PFun.mem_dom, (dbi.relations rn).validSchema _ left_2, DatabaseInstance.validSchema]; exact h
              have hv' := hv
              sorry
            . intro a' ha'
              sorry
          · intro h₁ h₂ h₃
            apply (right_1 ra).2.2
            . sorry
            . sorry
        . sorry

theorem relJoins.evalT_relation_def {dbi : DatabaseInstance String String μ} [Fintype (adomRs dbi.schema)] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
  RA.Query.evaluateT dbi (relJoins (RelationSchema.ordering (dbi.schema rn)) ts brs u) =
  {t | ∃t' : String →. μ, t' ∈ (dbi.relations rn).tuples ∧ (∀ra ∈ dbi.schema rn, t' ra = t (renamePairFunc ra ts brs u ra)) ∧ (∀a ∉ (dbi.schema rn).image (renamer ts brs u), t a = .none)} := by
    ext t
    sorry

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

theorem eq_comp_renamer {t : String →. μ} {dbi : DatabaseInstance String String μ} {rs : Finset String} [folStruc dbi] [Nonempty μ] {tDom : t.Dom = ↑rs} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h₁ : ∀i, TermtoAtt brs (ts i) ∈ rs) (h₂ : u ∉ rs)
  :
    (fun att ↦ dite (att ∈ dbi.schema rn)
      (λ h => Part.some (Term.realize (Sum.elim (TupleToFun tDom) (TupleToFun tDom ∘ FreeMap n brs)) (ts (RelationSchema.index h))))
      (λ _ => Part.none)
    ) = t ∘ renamer ts brs u := by
      ext a v
      simp_all
      apply Iff.intro
      · intro a_1
        split at a_1
        next h' =>
          simp_all only [Part.mem_some_iff]
          subst a_1
          have := h₁ (RelationSchema.index h')
          have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index h'))
          simp [hk]
          cases k with
          | inl val =>
            simp only [renamer]
            rw [RelationSchema.index?_eq_index_if_mem h']
            simp_all only [TermtoAtt, Option.map_some, Function.comp_apply, Option.getD_some,
              Sum.elim_inl, TupleToFun]
            by_cases hc : (t val).Dom
            . simp_all [Part.getOrElse_of_dom, Part.get_mem]
            . simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
          | inr val_1 =>
            simp only [renamer]
            rw [RelationSchema.index?_eq_index_if_mem h']
            simp_all only [TermtoAtt, Option.map_some, Function.comp_apply, Option.getD_some,
              Sum.elim_inr, TupleToFun]
            by_cases hc : (t (FreeMap n brs val_1)).Dom
            . simp_all [Part.getOrElse_of_dom, Part.get_mem]
            . simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        next h' => simp_all only [Part.notMem_none]

      · intro a_1
        split
        next h' =>
          have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index h'))
          simp_all only [renamer, RelationSchema.index?_eq_index_if_mem, Option.map_some,
            Function.comp_apply, Option.getD_some, Term.realize_var, Part.mem_some_iff, TermtoAtt]
          cases k with
          | inl val =>
            have := Part.dom_iff_mem.mpr (Exists.intro v a_1)
            simp_all only [← Part.get_eq_iff_mem, Sum.elim_inl, TupleToFun,
              Part.getOrElse_of_dom]
          | inr val_1 =>
            have := Part.dom_iff_mem.mpr (Exists.intro v a_1)
            simp_all only [← Part.get_eq_iff_mem, Sum.elim_inr, Function.comp_apply,
              TupleToFun, Part.getOrElse_of_dom]
        next h' =>
          simp_all only [Part.notMem_none]
          simp [renamer.notMem_def h'] at a_1
          apply h₂
          rw [← Finset.mem_coe, ← tDom, PFun.mem_dom]
          use v


noncomputable def relToRA (rn : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (rs brs : Finset String) (u : String) : RA.Query String String :=
    .p (rs) ((RA.Query.p ((dbs rn).image (renamer ts brs u)) (relJoins (RelationSchema.ordering (dbs rn)) ts brs u)).j (adom dbs rs))

theorem relToRA.schema_def : (relToRA dbs rn ts rs brs u).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA dbs rn ts rs brs u) := by
    simp [relToRA, relJoins.isWellTyped_def, adom.isWellTyped_def, adom.schema_def, relJoins.schema_def, renamePairFunc]

theorem relToRA.evalT_def [Nonempty (adomRs dbi.schema)] [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hrs : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) (hu : u ∉ rs) :
    RA.Query.evaluateT dbi (relToRA dbi.schema rn ts rs brs u) =
    {t | ∃h, RealizeDomSet (μ := μ) (Relations.boundedFormula (relations.R rn) ts) rs brs t h} := by
      simp_rw [RealizeDomSet, BoundedFormula.realize_rel]
      rw [← fol.Rel]
      simp_rw [folStruc_apply_RelMap, ArityToTuple.def_dite]
      simp only [relToRA, RA.Query.evaluateT, exists_and_right]

      have h₁ : ∀ (i : Fin (dbi.schema rn).card), TermtoAtt brs (ts i) ∈ rs := by
        intro i
        have ⟨k, hk⟩ := Term.cases (ts i)
        apply hrs
        cases k with
        | inl val =>
          simp [TermtoAtt, hk]
          apply Or.inl
          use i
          simp [hk]
        | inr val_1 =>
          simp [TermtoAtt, hk]

      have image_sub : Finset.image (renamer ts brs u) (dbi.schema rn) ⊆ rs := by
        apply Finset.image_subset_iff.mpr
        intro a ha
        simp [renamer]
        simp_all only [nonempty_subtype, RelationSchema.index?_eq_index_if_mem, Option.map_some, Function.comp_apply,
          Option.getD_some]



      ext t
      simp_all only [adom.complete_def, Set.mem_setOf_eq, relJoins.evalT_relation_def]
      apply Iff.intro
      · intro a

        have tDom : t.Dom = ↑rs := by sorry

        obtain ⟨w_1, h_1⟩ := a
        obtain ⟨left, right⟩ := h_1
        obtain ⟨w_2, h_1⟩ := left
        obtain ⟨left, right_1⟩ := h_1
        obtain ⟨w_3, h_1⟩ := right_1
        obtain ⟨left_1, right_1⟩ := h_1
        obtain ⟨left_1, right_2⟩ := left_1
        obtain ⟨w_4, h_1⟩ := left_1
        obtain ⟨left_1, right_2⟩ := right_2
        obtain ⟨left_2, right_3⟩ := h_1
        obtain ⟨w_5, h_1⟩ := right_3
        obtain ⟨w_6, h_2⟩ := left
        obtain ⟨left, right_3⟩ := h_2
        obtain ⟨w_7, h_2⟩ := left
        obtain ⟨left, right_4⟩ := h_2
        obtain ⟨left_3, right_4⟩ := right_4
        simp_all only [forall_exists_index, not_exists, and_imp, Finset.mem_image, not_and,
            Finset.coe_inj, exists_true_left, TupleToFun.tuple_eq_self]

        apply And.intro
        · rw [eq_comp_renamer (dbi := dbi) (rn := rn) (n := n) (brs := brs) (ts := ts) h₁ hu]
          convert left
          ext a v
          by_cases hc : a ∈ Finset.image (renamer ts brs u) (dbi.schema rn)
          . sorry
            -- rw [(right a).1 (image_sub hc)]
            -- simp at right_1
            -- sorry
          .
            sorry
        · sorry
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w_1, h_1⟩ := left

        have t_sub : ↑((dbi.schema rn).image (renamer ts brs u)) ⊆ t.Dom := by rw [w_1]; exact image_sub


        rw [eq_comp_renamer (dbi := dbi) (rn := rn) (n := n) (brs := brs) (ts := ts) h₁ hu] at h_1
        . use t
          apply And.intro
          . use t.restrict t_sub
            apply And.intro
            . use t.restrict t_sub
              apply And.intro
              . use t ∘ renamer ts brs u
                apply And.intro h_1 (And.intro ?_ ?_)
                · intro ra a
                  simp [renamePairFunc]
                  ext v
                  simp_all
                  intro h
                  use ra
                · intro a a_1
                  ext v
                  simp_all
              . intro a
                simp_all only [Finset.mem_image, Finset.coe_image, implies_true, not_exists, not_and, true_and]
                intro a_1
                ext a_2 : 1
                simp_all only [PFun.mem_restrict, Set.mem_image, Finset.mem_coe, Part.notMem_none, iff_false, not_and,
                  isEmpty_Prop, not_exists, not_false_eq_true, implies_true, IsEmpty.forall_iff]
            . use t
              apply And.intro
              . simp [w_1, right]
                use rn
                apply And.intro
                . simp [adomRs]
                  sorry
                . use t ∘ renamer ts brs u
              . exact joinSingleT.restrict t
          . simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, w_1]

noncomputable def toRA
  (f : (fol dbs).BoundedFormula String n) (rs brs : Finset String) (hn : n + depth f < brs.card) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt brs t₁) (TermtoAtt brs t₂) (adom dbs rs)
    | .rel (.R rn) ts => relToRA dbs rn ts rs brs (FreshString rs)
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
        | R rn => exact relToRA.evalT_def h FreshString.notMem_rs


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
