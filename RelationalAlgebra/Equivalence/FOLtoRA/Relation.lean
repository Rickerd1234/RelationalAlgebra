import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.Term
import RelationalAlgebra.Equivalence.FOLtoRA.RealizeDomSet
import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.RA.EquivRules
import RelationalAlgebra.Basic

open RM FOL FirstOrder Language

variable {μ : Type}

noncomputable def renamePair {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
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


noncomputable def combinePair {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
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


noncomputable def relJoins {dbs : String → Finset String} (ras : List String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
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

theorem relJoins.evalT_def' {dbi : DatabaseInstance String String μ} {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (h : ras.toFinset ⊆ dbi.schema rn) (hdisj : dbi.schema rn ∩ ras.toFinset.image (renamer ts brs u) = ∅) :
    RA.Query.evaluateT dbi (relJoins ras ts brs u) =
    {t | ∃t' : String →. μ, t' ∈ (dbi.relations rn).tuples ∧
      (
        ∀ra ∈ dbi.schema rn,
          t' ra = t ra ∧
          (ra ∈ ras → t' ra = t (renamePairFunc ra ts brs u ra))
      ) ∧ (
        ∀a ∉ dbi.schema rn ∪ (ras.toFinset.image (renamer ts brs u)),
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
        rw [ih (by simp_all; grind) (by simp_all; grind)]
        ext t

        have hhd : hd ∈ dbi.schema rn := by simp at h; grind
        have htl : tl.toFinset ⊆ dbi.schema rn := by simp at h; grind

        simp [combinePair.evalT_def]

        sorry

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

noncomputable def relJoinsMin {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : RA.Query String String :=
  .p ((dbs rn).image (renamer ts brs u)) (relJoins (RelationSchema.ordering (dbs rn)) ts brs u)

theorem relJoinsMin.evalT_def {dbi : DatabaseInstance String String μ} [Fintype (adomRs dbi.schema)] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hdisj : (dbi.schema rn) ∩ (dbi.schema rn).image (renamer ts brs u) = ∅) :
    RA.Query.evaluateT dbi (relJoinsMin ts brs u) =
    {t | ∃t' : String →. μ, t' ∈ (dbi.relations rn).tuples ∧ (∀ra ∈ dbi.schema rn, t' ra = t (renamePairFunc ra ts brs u ra)) ∧ (∀a ∉ (dbi.schema rn).image (renamer ts brs u), t a = .none)} := by
      ext t
      rw [relJoinsMin, RA.Query.evaluateT]
      rw [relJoins.evalT_def' (by simp) (by simp [hdisj])]
      simp [renamePairFunc]
      sorry

theorem relJoinsMin.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relJoinsMin ts brs u).schema dbs = (dbs rn).image (renamer ts brs u) := rfl

theorem relJoinsMin.isWellTyped_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
    RA.Query.isWellTyped dbs (relJoinsMin ts brs u) := by
      simp [relJoinsMin, relJoins.schema_def, relJoins.isWellTyped_def, renamePairFunc]

variable {dbs : String → Finset String} [Fintype (adomRs dbs)]

noncomputable def relToRA (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (rs brs : Finset String) (u : String) : RA.Query String String :=
    .p (rs) ((relJoinsMin ts brs u).j (adom dbs rs))

theorem relToRA.schema_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  (relToRA ts rs brs u).schema dbs = rs := rfl

theorem relToRA.isWellTyped_def [Nonempty ↑(adomRs dbs)] {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  RA.Query.isWellTyped dbs (relToRA ts rs brs u) := by
    simp [relToRA, relJoinsMin.isWellTyped_def, adom.isWellTyped_def, adom.schema_def]

theorem relToRA.evalT_def [Nonempty (adomRs dbi.schema)] [Fintype (adomRs dbi.schema)] [folStruc dbi] [Nonempty μ] {ts : Fin (dbi.schema rn).card → (fol dbi.schema).Term (String ⊕ Fin n)}
  (hrs : (Finset.univ.biUnion fun i ↦ (ts i).varFinsetLeft) ∪ FRan (FreeMap n brs) ⊆ rs) (hu : u ∉ rs) (hdisj : (dbi.schema rn) ∩ (dbi.schema rn).image (renamer ts brs u) = ∅) :
    RA.Query.evaluateT dbi (relToRA ts rs brs u) =
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

      have renamer_sub : ∀a ∈ (dbi.schema rn), renamer ts brs u a ∈ rs := by
        intro a ha
        simp [renamer]
        simp_all only [nonempty_subtype, RelationSchema.index?_eq_index_if_mem, Option.map_some, Function.comp_apply,
          Option.getD_some]

      have image_sub : Finset.image (renamer ts brs u) (dbi.schema rn) ⊆ rs := by
        apply Finset.image_subset_iff.mpr renamer_sub

      ext t
      simp_all only [adom.complete_def, Set.mem_setOf_eq, relJoinsMin.evalT_def]
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
            . rw [(right (renamer ts brs u a)).1 (renamer_sub a hc), renamePairFunc, renameFunc.old_def]
          . by_cases hc' : renamer ts brs u a ∈ rs
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

        have t_sub : ↑((dbi.schema rn).image (renamer ts brs u)) ⊆ t.Dom := by rw [w_1]; exact image_sub


        rw [eq_comp_renamer (dbi := dbi) (rn := rn) (n := n) (brs := brs) (ts := ts) h₁ hu] at h_1
        . use t
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
