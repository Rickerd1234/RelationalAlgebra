import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.Term
import RelationalAlgebra.Equivalence.FOLtoRA.RealizeDomSet
import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.RA.EquivRules
import RelationalAlgebra.Basic

open RM FOL FirstOrder Language

variable {μ : Type}

def renamePair {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .r (renamePairFunc ra ts brs) (.R rn)

theorem renamePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (renamePair ra ts brs).schema dbs = (dbs rn).image (renamePairFunc ra ts brs) := rfl

theorem renamePair.schema_update_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) (h' : renamer ts brs ra ∉ dbs rn) :
  (renamePair ra ts brs).schema dbs = (insert (renamer ts brs ra) (dbs rn)).erase ra  := by
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
    RA.Query.isWellTyped dbs (renamePair ra ts brs) := by
      simp [renamePair, renamePairFunc, rename_func_bijective]

theorem renamePair.evalT_def {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
    RA.Query.evaluateT dbi (renamePair ra ts brs) =
      {t | t ∘ (renamePairFunc ra ts brs) ∈ (dbi.relations rn).tuples} := by
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


def combinePair {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .j (renamePair ra ts brs) (.R rn)

theorem combinePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  (combinePair ra ts brs).schema dbs = dbs rn ∪ {renamePairFunc ra ts brs ra} := by
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
    RA.Query.isWellTyped dbs (combinePair ra ts brs) := by
      simp [combinePair, renamePair.isWellTyped_def]

theorem combinePair.evalT_def {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
  RA.Query.evaluateT dbi (combinePair ra ts brs) =
    {t : String →. μ | ∃t₁ ∈ (dbi.relations rn).tuples, ∃t₂, t₂ ∘ (renamePairFunc ra ts brs) ∈ (dbi.relations rn).tuples ∧
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

        have ht₂' : t₂ ∈ RA.Query.evaluateT dbi (renamePair ra ts brs) := by simp [renamePair.evalT_def, ht₂]

        have t₂Dom := RA.Query.evaluate.validSchema (renamePair ra ts brs) renamePair.isWellTyped_def t₂ ht₂'
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

def prunePair {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .s ra (renamer ts brs ra) (combinePair ra ts brs)

theorem prunePair.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (prunePair ra ts brs).schema dbs = (combinePair ra ts brs).schema dbs := by
    simp [prunePair]

theorem prunePair.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn):
    RA.Query.isWellTyped dbs (prunePair ra ts brs) := by
      simp [prunePair, combinePair.isWellTyped_def, combinePair.schema_def, h, renamePairFunc]

theorem prunePair.evalT_def {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)} :
  RA.Query.evaluateT dbi (prunePair ra ts brs) =
    {t : String →. μ | (∃t₁ ∈ (dbi.relations rn).tuples, ∃t₂, t₂ ∘ (renamePairFunc ra ts brs) ∈ (dbi.relations rn).tuples ∧
          ∀a, (a ∈ t₁.Dom → t a = t₁ a) ∧ (a ∈ PFun.Dom t₂ → t a = t₂ a) ∧ (a ∉ t₁.Dom ∪ PFun.Dom t₂ → t a = .none)) ∧ (t ra = t (renamer ts brs ra))
    } := by
      simp only [prunePair, RA.Query.evaluateT.eq_2, selectionT, combinePair.evalT_def,
        Set.mem_setOf_eq]

def relJoins {dbs : String → Finset String} (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  ras.foldr (λ ra sq => .j (prunePair ra ts brs) sq) (.R rn)

theorem relJoins.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ras.toFinset ⊆ dbs rn) :
  (relJoins ras ts brs).schema dbs = (ras.toFinset.image (λ ra => renamePairFunc ra ts brs ra)) ∪ (dbs rn) := by
    simp [relJoins]
    induction ras with
    | nil => simp_all
    | cons hd tl ih =>
      have hhd : hd ∈ dbs rn := by simp at h; grind
      have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
      simp_all only [forall_const, List.toFinset_cons, List.foldr_cons, RA.Query.schema.eq_4,
        RA.Query.schema, Finset.insert_union, Finset.image_insert, prunePair.schema_def, combinePair.schema_def]
      simp_all only [Finset.union_singleton, Finset.insert_union]
      grind

theorem relJoins.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h: ras.toFinset ⊆ dbs rn) :
    RA.Query.isWellTyped dbs (relJoins ras ts brs) := by
      simp [relJoins]
      induction ras with
      | nil => simp
      | cons hd tl ih =>
        have hhd : hd ∈ dbs rn := by simp at h; grind
        have htl : tl.toFinset ⊆ dbs rn := by simp at h; grind
        simp only [List.foldr_cons, RA.Query.isWellTyped, prunePair.isWellTyped_def hhd, true_and]
        apply ih htl

theorem test {dbi : DatabaseInstance String String μ} (t' : String →. μ) :
  t' ∘ renamePairFunc hd ts brs ∈ (dbi.relations rn).tuples ↔ t' ∈ (dbi.relations rn).tuples.image (λ t => t ∘ renamePairFunc hd ts brs) := by
    simp_all
    apply Iff.intro
    · intro a_1
      use t' ∘ renamePairFunc hd ts brs
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

theorem relJoins.evalT_def' {dbi : DatabaseInstance String String μ} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : ras.toFinset ⊆ dbi.schema rn) (hdisj : dbi.schema rn ∩ ras.toFinset.image (renamer ts brs) = ∅) (hnodup : ras.Nodup) :
    RA.Query.evaluateT dbi (relJoins ras ts brs) =
    {t | ∃t' : String →. μ, t' ∈ (dbi.relations rn).tuples ∧
      (
        ∀ra ∈ dbi.schema rn,
          t' ra = t ra ∧
          (ra ∈ ras → t' ra = t (renamePairFunc ra ts brs ra))
      ) ∧ (
        ∀a ∉ dbi.schema rn ∪ (ras.toFinset.image (renamer ts brs)),
          t a = .none
      )
    } := by
      induction ras with
      | nil =>
        ext t
        simp only [relJoins, List.foldr_nil, RA.Query.evaluateT, List.not_mem_nil,
          IsEmpty.forall_iff, and_true, List.toFinset_nil, Finset.image_empty, Finset.union_empty,
          Set.mem_setOf_eq]
        apply Iff.intro
        . intro h
          use t
          simp_all [t_eq_none_if_notMem_schema h]
        . intro ⟨t', ht', ht₁', ht₂'⟩
          convert ht'
          ext a v
          by_cases hc : a ∈ dbi.schema rn
          . rw [ht₁' a hc]
          . rw [t_eq_none_if_notMem_schema ht' hc, ht₂' a hc]

      | cons hd tl ih =>
        simp only [List.mem_cons, List.toFinset_cons, Finset.image_insert, Finset.union_insert,
          Finset.mem_insert, Finset.mem_union, Finset.mem_image, List.mem_toFinset, not_or,
          not_exists, not_and, and_imp]
        rw [relJoins]
        rw [List.foldr_cons]
        rw [← relJoins]
        simp

        have hhd : hd ∈ dbi.schema rn := by simp at h; grind
        have htl : tl.toFinset ⊆ dbi.schema rn := by simp at h; grind

        have hdisj' : dbi.schema rn ∩ Finset.image (renamer ts brs) tl.toFinset = ∅ := by
          rw [List.toFinset_cons] at hdisj
          grind

        rw [ih htl hdisj' (List.Nodup.of_cons hnodup)]
        ext t

        simp [prunePair.evalT_def]

        apply Iff.intro
        . intro ⟨t₁, ⟨⟨t₃, ht₃, ⟨t₄, ht₄, ht₁⟩⟩, ht₁'⟩, t₂, ⟨t₅, ht₅, ht₂'⟩, ht⟩

          have t₄Dom' : PFun.Dom (t₄ ∘ renamePairFunc hd ts brs) = dbi.schema rn := by
            rw [← DatabaseInstance.validSchema, ← (dbi.relations rn).validSchema _ ht₄]

          have t₄Dom : PFun.Dom t₄ = (dbi.schema rn).image (renamePairFunc hd ts brs) := by
            ext a
            simp only [Finset.coe_image, Set.mem_image]
            rw [← t₄Dom']
            simp_rw [PFun.mem_dom, Function.comp_apply]
            apply Iff.intro
            . intro ⟨v, hv⟩
              use renamePairFunc hd ts brs a
              simp [renamePairFunc, rename_func_cancel_self]
              use v
            . intro ⟨a', ⟨v, hv⟩, ha⟩
              subst ha
              use v

          simp [Finset.ext_iff] at hdisj
          use (λ a => ite (a = hd) (t hd) (ite (a = renamer ts brs hd) (t₄ (renamePairFunc hd ts brs a)) (ite (a ∈ dbi.schema rn) (t a) (.none))))
          split_ands
          . convert ht₃ with ra
            simp_all only [not_false_eq_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset, not_or,
              not_exists, not_and, and_imp, forall_const, List.toFinset_cons, Finset.image_insert, Finset.mem_insert,
              or_false, Finset.coe_image]
            obtain ⟨left, right⟩ := ht₂'
            split_ifs
            next h_1 =>
              subst h_1
              have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₃ hhd
              rw [← (ht₁ ra).1 _ hv]
              rw [← (ht₁ ra).1 _ hv] at hv
              rw [(ht ra).1 _ hv]
            next h_1 =>
              subst h_1
              simp [renamePairFunc]
              have : t₄ hd = .none := by
                rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, t₄Dom]
                simp [renamePairFunc, renameFunc]
                intro x hx
                apply And.intro
                . exact (hdisj x hx).1
                . split_ifs with h'
                  . subst h'
                    simp [Eq.comm, (hdisj x hx).1]
                  . trivial

              simp [this, Eq.comm]
              apply t_eq_none_if_notMem_schema ht₃
              by_contra hc
              apply (hdisj _ hc).1
              rfl

            next h_1 =>
              have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₃ h_1
              rw [← (ht₁ ra).1 _ hv]
              rw [← (ht₁ ra).1 _ hv] at hv
              rw [(ht ra).1 _ hv]
            next h_1 => exact Eq.symm (t_eq_none_if_notMem_schema ht₃ h_1)
          . intro ra hra
            simp [hra]
            apply And.intro
            . split_ifs with h' h''
              . subst h'
                rfl
              . subst h''
                exact False.elim ((hdisj _ hra).1 rfl)
              . rfl
            . intro h₁
              split_ifs with h' h''
              . subst h'
                simp [renamePairFunc]
                have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₃ hra
                rw [← (ht₁ ra).1 _ hv] at hv
                rw [(ht ra).1 _ hv]
                rw [ht₁'] at ⊢ hv
                rw [← (ht _).1 _ hv]

              . subst h''
                exact False.elim ((hdisj _ hra).1 rfl)
              . cases h₁ with
                | inl h_1 =>
                  exact False.elim (h' h_1)

                | inr h_1 =>
                  have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₅ hra
                  rw [(ht₂'.1 ra hra).1] at hv
                  rw [(ht ra).2.1 _ hv]
                  rw [← (ht₂'.1 ra hra).1]
                  rw [← (ht₂'.1 ra hra).1] at hv
                  rw [(ht₂'.1 ra hra).2 h_1]
                  rw [(ht₂'.1 ra hra).2 h_1] at hv
                  rw [(ht _).2.1 _ hv]

          . intro a a_1 a_2 a_3
            apply (ht _).2.2
            . rw [← Part.eq_none_iff]
              apply (ht₁ _).2.2
              . rw [← Part.eq_none_iff, Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom,
                  (dbi.relations rn).validSchema _ ht₃, DatabaseInstance.validSchema]
                exact a_2
              . rw [← Part.eq_none_iff, Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, t₄Dom]
                simp [renamePairFunc]
                intro x hx
                by_cases hc : x = hd
                . subst hc
                  simp [renameFunc.old_def, Eq.comm, a_1]
                . by_cases hc' : x = renamer ts brs hd
                  . subst hc'
                    simp [renameFunc.new_def]
                    by_contra hc''
                    subst hc''
                    exact a_2 hhd
                  . simp [renameFunc, hc, hc']
                    by_contra hc''
                    subst hc''
                    exact a_2 hx
            . rw [ht₂'.2 a a_2 a_3]
              simp

        . intro ⟨t₁, ht₁, ht₁', ht⟩

          have helper : ∀a ∈ tl, ∀b ∈ tl, renamer ts brs a = renamer ts brs b → t₁ a = t₁ b := by
            intro a ha b hb h'
            have ha' := by apply htl (List.mem_toFinset.mpr ha)
            have hb' := by apply htl (List.mem_toFinset.mpr hb)
            rw [(ht₁' _ ha').2 (Or.inr ha)]
            rw [(ht₁' _ hb').2 (Or.inr hb)]
            simp [renamePairFunc, renameFunc.old_def, h']

          use λ a => ite (a ∈ dbi.schema rn ∨ a = renamer ts brs hd) (t a) (.none)
          apply And.intro
          . apply And.intro
            . use t₁
              apply And.intro ht₁
              use t₁ ∘ renamePairFunc hd ts brs
              have : (t₁ ∘ renamePairFunc hd ts brs) ∘ renamePairFunc hd ts brs = t₁ := by
                funext; simp [renamePairFunc, rename_func_cancel_self]

              simp [this, ht₁]

              intro a
              simp_all only [not_false_eq_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset, not_or,
                not_exists, not_and, and_imp, forall_const, List.toFinset_cons, Finset.image_insert,
                Finset.mem_insert, or_false, List.nodup_cons]
              obtain ⟨left, right⟩ := hnodup
              apply And.intro
              · intro x h_1
                have : a ∈ dbi.schema rn := by
                  rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ ht₁, PFun.mem_dom]
                  use x
                rw [if_pos (Or.inl this)]
                rw [(ht₁' a _).1]
                exact this
              · apply And.intro
                · intro x h_1
                  have ha' : (renamePairFunc hd ts brs a) ∈ dbi.schema rn := by
                    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ ht₁, PFun.mem_dom]
                    use x

                  by_cases hc : a = hd
                  . subst hc
                    rw [if_pos (Or.inl hhd)]
                    rw [← (ht₁' a hhd).1, (ht₁' a hhd).2 (Or.inl rfl), ← (ht₁' _ ha').1]
                  . by_cases hc' : a = renamer ts brs hd
                    . subst hc'
                      simp [renamePairFunc, renameFunc] at ha' h_1 ⊢
                      rw [(ht₁' _ hhd).2 (Or.inl rfl), renamePairFunc, renameFunc.old_def]
                    . simp [renamePairFunc, renameFunc, hc, hc'] at ha' ⊢
                      rw [if_pos ha']
                      rw [(ht₁' a ha').1]
                · intro a_1 a_2 a_3

                  have ha' : a ∉ dbi.schema rn := by
                    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ ht₁]
                    simp only [PFun.mem_dom, a_1, exists_false, not_false_eq_true]

                  apply ht
                  . by_contra hc
                    subst hc
                    simp [renamePairFunc] at a_2
                    have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₁ hhd
                    apply a_2 v hv
                  . apply ha'
                  . intro x hx
                    by_contra hc
                    subst hc
                    simp [ha'] at a_3
                    simp [a_3, renamePairFunc] at a_2
                    have ⟨v, hv⟩ := t_ex_v_if_mem_schema ht₁ hhd
                    apply a_2 v hv
            . simp [renamePairFunc] at ht₁'
              simp only [hhd, true_or, ↓reduceIte, or_true]
              rw [← (ht₁' hd hhd).2 (Or.inl rfl), (ht₁' hd hhd).1]
          . let := ∀a, ∀h : a ∈ tl.toFinset.image (renamer ts brs), ∃f : String → String, f a = renamePairFunc (f a) ts brs a

            use λ a => ite (a ∈ tl.toFinset) (t₁ a) (ite (a ∈ dbi.schema rn) (t a) (ite (a = renamer ts brs hd) (t₁ a) (ite (a ∈ tl.toFinset.image (renamer ts brs)) (t₁ sorry) .none)))
            apply And.intro
            use λ a => ite (a ∈ tl) (t (renamePairFunc a ts brs a)) (t₁ a)
            split_ands
            . convert ht₁ with a'
              split_ifs with h₁
              . rw [(ht₁' a' (htl (List.mem_toFinset.mpr h₁))).2 (Or.inr h₁)]
              . rfl
            . intro ra hra
              simp_all only [not_false_eq_true, Finset.mem_union, Finset.mem_image,
                List.mem_toFinset, not_or, not_exists, not_and, and_imp, forall_const,
                List.toFinset_cons, Finset.image_insert, Finset.mem_insert, or_false,
                List.nodup_cons, ↓reduceIte]
              obtain ⟨left, right⟩ := hnodup
              split
              next h_1 =>
                simp_all only [forall_const]
                apply And.intro
                · rw [← (ht₁' ra hra).2 (Or.inr h_1), (ht₁' ra hra).1]
                · split
                  next h_2 =>
                    rw [← (ht₁' ra hra).2 (Or.inr h_1)]
                    have : renamePairFunc ra ts brs ra ∈ dbi.schema rn :=
                      by apply htl (List.mem_toFinset.mpr h_2)
                    rw [(ht₁' _ this).1, ← (ht₁' ra hra).2 (Or.inr h_1)]
                  next h_2 =>
                    simp_all only [left_eq_ite_iff]
                    intro a
                    split
                    next h_3 =>
                      simp_all only [not_false_eq_true, Finset.inter_insert_of_notMem]
                      sorry
                    next h_3 =>
                      split
                      next h_4 =>
                        obtain ⟨w, h_4⟩ := h_4
                        obtain ⟨left_1, right_1⟩ := h_4
                        have ⟨k, hk₁, hk₂, hk₃⟩ := renamer_inv_r.ex_def (ts := ts) (brs := brs) (List.mem_toFinset.mpr h_1) htl
                        -- rw [renamePairFunc, renameFunc.old_def, ← hk₁]
                        simp [renamePairFunc] at ht₁' right_1
                        -- rw [(ht₁' _ hk₂).2 (Or.inr (List.mem_dedup.mp hk₃))]
                        -- rw [← right_1]
                        -- rw [← (ht₁' _ (htl (List.mem_toFinset.mpr left_1))).2 (Or.inr left_1)]
                        -- apply helper _ left_1 _ (List.mem_dedup.mp hk₃)

                        sorry
                      next h_4 => simp_all only [not_exists, not_and, not_false_eq_true, implies_true]
              next
                h_1 =>
                simp_all [false_or, left_eq_ite_iff, not_exists, not_and, not_isEmpty_of_nonempty,
                  IsEmpty.forall_iff, and_true]

            · intro ra a a_1
              simp_all only [not_false_eq_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset, not_or,
                not_exists, not_and, and_imp, forall_const, List.toFinset_cons, Finset.image_insert,
                Finset.mem_insert, or_false, List.nodup_cons]
              obtain ⟨left, right⟩ := hnodup
              simp_all only [↓reduceIte]
              split
              next h_1 => exact t_eq_none_if_notMem_schema ht₁ a
              next h_1 =>
                -- simp_all only [ite_eq_right_iff]
                -- intro a_2
                -- cases a_2 with
                -- | inl h_2 =>
                --   subst h_2
                --   simp_all only [not_false_eq_true, Finset.inter_insert_of_notMem]
                --   sorry
                -- | inr h_3 =>
                --   obtain ⟨w, h_2⟩ := h_3
                --   obtain ⟨left_1, right_1⟩ := h_2
                --   subst right_1
                  sorry
            . intro a
              simp_all only [not_false_eq_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset, not_or,
                not_exists, not_and, and_imp, forall_const, List.toFinset_cons, Finset.image_insert,
                Finset.mem_insert, or_false, List.nodup_cons, left_eq_ite_iff]
              obtain ⟨left, right⟩ := hnodup
              split
              next h_1 =>
                cases h_1 with
                | inl
                  h_2 =>
                  simp_all only [not_true_eq_false, not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true,
                    ↓reduceIte, ite_self, not_false_eq_true, forall_const, true_and]
                  intro a_1
                  exact Part.eq_none_iff.mpr a_1
                | inr h_3 =>
                  subst h_3
                  simp_all only [not_true_eq_false, not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true,
                    true_or, ↓reduceIte, true_and]
                  split
                  next h_1 =>
                    apply And.intro
                    · intro x h_2
                      have := schema_mem_if_exists_v ht₁ h_2
                      simp [this, ht₁']
                    · intro a a_1
                      exact Part.eq_none_iff.mpr a
                  next h_1 =>
                    simp_all only [left_eq_ite_iff]
                    split
                    next h_2 => simp_all only [Finset.inter_insert_of_mem, insert_empty_eq, Finset.singleton_ne_empty]
                    next h_2 =>
                      simp_all only [not_false_eq_true, Finset.inter_insert_of_notMem, forall_const]
                      apply And.intro
                      · intro x h_3
                        have := schema_mem_if_exists_v ht₁ h_3
                        simp [this, ht₁']
                      · intro a a_1
                        exact Part.eq_none_iff.mpr a
              next
                h_1 =>
                simp_all only [not_or, Part.notMem_none, not_true_eq_false, not_isEmpty_of_nonempty,
                  IsEmpty.forall_iff, imp_self, implies_true, ↓reduceIte, false_or, not_false_eq_true, forall_const,
                  true_and]
                obtain ⟨left_1, right_1⟩ := h_1
                split
                next h_1 =>
                  apply And.intro
                  · intro x h_2
                    have := schema_mem_if_exists_v ht₁ h_2
                    simp [this, ht₁']
                  · intro a_1
                    apply ht
                    . exact right_1
                    . exact left_1
                    . intro x a_2
                      apply Aesop.BuiltinRules.not_intro
                      intro a_3
                      subst a_3
                      apply left_1
                      apply htl
                      exact List.mem_toFinset.mpr h_1
                next h_1 =>
                  split
                  next h_2 =>
                    obtain ⟨w, h_2⟩ := h_2
                    obtain ⟨left_2, right_2⟩ := h_2
                    subst right_2
                    apply And.intro
                    · intro x h_2
                      have := schema_mem_if_exists_v ht₁ h_2
                      simp [this, ht₁']
                      sorry
                    · intro a
                      apply ht
                      . exact right_1
                      . exact left_1
                      . intro x a_2
                        apply Aesop.BuiltinRules.not_intro
                        intro a_3
                        sorry
                  next h_2 =>
                    simp_all only [not_exists, not_and, Part.notMem_none, not_true_eq_false, implies_true,
                      not_false_eq_true, imp_self, and_self]

theorem eq_comp_renamer {t : String →. μ} {dbi : DatabaseInstance String String μ} {rs : Finset String} [folStruc dbi] [Nonempty μ] {tDom : t.Dom = ↑rs} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h₁ : ∀i, TermtoAtt brs (ts i) ∈ rs) (h₂ : default ∉ rs)
  :
    (fun att ↦ dite (att ∈ dbi.schema rn)
      (λ h => Part.some (Term.realize (Sum.elim (TupleToFun tDom) (TupleToFun tDom ∘ FreeMap n brs)) (ts (RelationSchema.index h))))
      (λ _ => Part.none)
    ) = t ∘ renamer ts brs := by
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

def relJoinsMin {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : RA.Query String String :=
  .p ((dbs rn).image (renamer ts brs)) (relJoins (RelationSchema.ordering (dbs rn)) ts brs)

theorem relJoinsMin.evalT_def {dbi : DatabaseInstance String String μ} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hdisj : (dbi.schema rn) ∩ (dbi.schema rn).image (renamer ts brs) = ∅) (hu : default ∉ (dbi.schema rn).image (renamer ts brs)) :
    RA.Query.evaluateT dbi (relJoinsMin ts brs) =
    {t | ∃t' : String →. μ, t' ∈ (dbi.relations rn).tuples ∧ (∀ra ∈ dbi.schema rn, t' ra = t (renamePairFunc ra ts brs ra)) ∧ (∀a ∉ (dbi.schema rn).image (renamer ts brs), t a = .none)} := by
      ext t
      rw [relJoinsMin, RA.Query.evaluateT]
      rw [relJoins.evalT_def' (by simp) (by simp [hdisj]) (by simp)]
      simp [renamePairFunc]
      simp_all only [forall_const]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := left
        obtain ⟨left, right_1⟩ := h
        obtain ⟨left_1, right_1⟩ := right_1
        simp_all only [not_false_eq_true, implies_true, and_true]
        use w_1
        simp_all only [true_and]
        intro ra hra
        rw [(right (renamer ts brs ra)).1 ra hra rfl]
        rw [← (left_1 ra hra).1]
        rw [← (left_1 ra hra).2]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only [not_false_eq_true, implies_true, and_true, forall_apply_eq_imp_iff₂]

        simp [Finset.ext_iff] at hdisj

        haveI : ∀a, Decidable (w a).Dom := by exact fun a ↦ Classical.propDecidable (w a).Dom
        haveI : ∀a, Decidable (t a).Dom := by exact fun a ↦ Classical.propDecidable (t a).Dom

        use λ a => ite (w a).Dom (w a) (ite (t a).Dom (t a) (.none))
        apply And.intro
        · use t ∘ renamer ts brs
          apply And.intro
          . convert left
            ext a v
            simp
            by_cases hc : a ∈ dbi.schema rn
            . simp_all
            . simp_all [t_eq_none_if_notMem_schema left hc]
              rw [right (renamer ts brs a) (?_)]
              . simp
              . intro x a_1
                apply Aesop.BuiltinRules.not_intro
                intro a_2
                nth_rw 2 [renamer] at a_2
                simp [RelationSchema.index?_none.mpr hc] at a_2
                simp_all

          apply And.intro
          · intro ra hra
            simp_all only [Finset.mem_image, not_exists, not_and, Function.comp_apply,
              not_false_eq_true, implies_true, Part.not_none_dom, ↓reduceIte, left_eq_ite_iff]
            split
            next h =>
              apply And.intro
              · intro a
                exact Part.eq_none_iff'.mpr a
              · rw [Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema _ left,
                  DatabaseInstance.validSchema] at h
                exact False.elim (hdisj (renamer ts brs ra) h ra hra rfl)
            next h =>
              simp_all only [left_eq_ite_iff, and_self]
              intro a
              exact Part.eq_none_iff'.mpr a
          · intro a a_1 a_2
            simp_all only [Finset.mem_image, not_exists, not_and, not_false_eq_true, implies_true,
              Part.not_none_dom, ↓reduceIte, ite_eq_right_iff]
            intro h
            exact t_eq_none_if_notMem_schema left a_1
        · simp_all only [Finset.mem_image, not_exists, not_and]
          intro a a_1
          split
          next h =>
            rw [Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema _ left,
              DatabaseInstance.validSchema] at h
            exact False.elim (hdisj (renamer ts brs a) h a a_1 rfl)
          next h =>
            simp_all only [left_eq_ite_iff]
            intro a_2
            exact Part.eq_none_iff'.mpr a_2

theorem relJoinsMin.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relJoinsMin ts brs).schema dbs = (dbs rn).image (renamer ts brs) := rfl

theorem relJoinsMin.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
    RA.Query.isWellTyped dbs (relJoinsMin ts brs) := by
      simp [relJoinsMin, relJoins.schema_def, relJoins.isWellTyped_def, renamePairFunc]

variable {dbs : String → Finset String} [Fintype (adomRs dbs)]

noncomputable def relToRA (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (rs brs : Finset String) : RA.Query String String :=
    .p (rs) ((relJoinsMin ts brs).j (adom dbs rs))

theorem relToRA.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relToRA ts rs brs).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA ts rs brs) := by
    simp [relToRA, relJoinsMin.isWellTyped_def, adom.isWellTyped_def, adom.schema_def]

theorem relToRA.evalT_def [Nonempty (adomRs dbi.schema)] [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hrs : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) (hu : default ∉ rs) (hdisj : (dbi.schema rn) ∩ (dbi.schema rn).image (renamer ts brs) = ∅) :
    RA.Query.evaluateT dbi (relToRA ts rs brs) =
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

      have renamer_sub : ∀a ∈ (dbi.schema rn), renamer ts brs a ∈ rs := by
        intro a ha
        simp [renamer]
        simp_all only [nonempty_subtype, RelationSchema.index?_eq_index_if_mem, Option.map_some, Function.comp_apply,
          Option.getD_some]

      have image_sub : Finset.image (renamer ts brs) (dbi.schema rn) ⊆ rs := by
        apply Finset.image_subset_iff.mpr renamer_sub

      ext t
      simp_all only [adom.complete_def, Set.mem_setOf_eq, relJoinsMin.evalT_def hdisj (by grind)]
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
        simp_all only [not_exists, Finset.mem_image, not_and,
          Finset.coe_inj, exists_true_left, TupleToFun.tuple_eq_self]

        apply And.intro
        · rw [eq_comp_renamer (dbi := dbi) (rn := rn) (n := n) (brs := brs) (ts := ts) h₁ hu]
          convert left
          ext a v
          by_cases hc : a ∈ dbi.schema rn
          . simp only [Function.comp_apply]
            have ⟨v, hv⟩ : ∃v, v ∈ w_6 a := by
              rw [← PFun.mem_dom, (dbi.relations rn).validSchema _ left, DatabaseInstance.validSchema]
              exact hc
            rw [(right_3).1 a hc] at ⊢ hv
            simp at right_1
            rw [← (right_1 _).1 v hv]
            . rw [(right (renamer ts brs a)).1 (renamer_sub a hc), renamePairFunc, renameFunc.old_def]
          . by_cases hc' : renamer ts brs a ∈ rs
            . simp [renamer, RelationSchema.index?_none.mpr hc] at hc'
              exact False.elim (hu hc')
            . simp only [Function.comp_apply, not_false_eq_true, Part.notMem_none, false_iff, hc', right]
              revert v
              rw [← not_exists, ← PFun.mem_dom, (dbi.relations rn).validSchema _ left, DatabaseInstance.validSchema]
              exact hc
        · sorry
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w_1, h_1⟩ := left

        have t_sub : ↑((dbi.schema rn).image (renamer ts brs)) ⊆ t.Dom := by rw [w_1]; exact image_sub


        rw [eq_comp_renamer (dbi := dbi) (rn := rn) (n := n) (brs := brs) (ts := ts) h₁ hu] at h_1
        . use t
          apply And.intro
          . use t.restrict t_sub
            apply And.intro
            . use t ∘ renamer ts brs
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
            . use t
              apply And.intro
              . simp [w_1, right]
                use rn
                apply And.intro
                . simp [adomRs]
                  sorry
                . use t ∘ renamer ts brs
              . exact joinSingleT.restrict t
          . simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, w_1]
