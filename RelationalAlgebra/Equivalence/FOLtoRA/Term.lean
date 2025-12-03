import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.ModelTheory
import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Variable
import RelationalAlgebra.Util.Util

open RM FOL FirstOrder Language

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

noncomputable def renamePairFunc {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u : String) : String → String :=
  renameFunc ra (renamer ts brs u ra)

noncomputable def getRAs {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (u a : String) : Finset String :=
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
