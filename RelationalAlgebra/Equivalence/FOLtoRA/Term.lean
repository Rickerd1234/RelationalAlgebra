import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.ModelTheory
import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Variable
import RelationalAlgebra.Util.Util

open RM FOL FirstOrder Language

def TermtoAtt (brs : Finset String) : (fol dbs).Term (String ⊕ Fin n) → String
  | var (Sum.inl s) => s
  | var (Sum.inr i) => FreeMap n brs i
  | _ => default


def TermfromAtt {brs : Finset String} (hn : n ≤ brs.card) : String → (fol dbs).Term (String ⊕ Fin n) :=
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



def renamer {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (ra : String) : String :=
  ((RelationSchema.index? (dbs rn) ra).map (TermtoAtt brs ∘ ts)).getD (default)

theorem renamer.notMem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∉ dbs rn) :
  renamer ts brs ra = default := by
    rw [renamer, RelationSchema.index?_none.mpr h, Option.map_none, Option.getD_none]

theorem renamer.mem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  renamer ts brs ra = (TermtoAtt brs ∘ ts) (RelationSchema.index h) := by
    have ⟨k, hk⟩ := RelationSchema.index?_isSome_eq_iff.mp (RelationSchema.index?_isSome.mpr h)
    rw [RelationSchema.index]
    simp_rw [renamer, hk, Option.map_some, Option.getD_some, Option.get]

def renamePairFunc {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : String → String :=
  renameFunc ra (renamer ts brs ra)

def getRAs {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) : Finset String :=
  (dbs rn).filter (λ ra => renamer ts brs ra = a)

theorem getRAs.mem_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {a : String} :
  ra ∈ getRAs ts brs a ↔ ra ∈ dbs rn ∧ renamer ts brs ra = a := by simp [getRAs]

instance {dbs} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} : Fintype ↑{ra | ra ∈ dbs rn ∧ renamer ts brs ra = a} := by
  apply Fintype.ofFinset (getRAs ts brs a)
  intro ra
  simp [Set.mem_setOf_eq.mp getRAs.mem_def]

theorem getRAs.def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} {a : String} :
  getRAs ts brs a = {ra | ra ∈ dbs rn ∧ renamer ts brs ra = a} := by simp [getRAs]


def renamer_inv_r {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs rs : Finset String) (a : String) : String :=
  (RelationSchema.ordering ((getRAs ts brs a) ∩ rs)).headD default

theorem renamer_inv_r.mem_inter_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ getRAs ts brs x) (h' : ra ∈ rs) :
  renamer_inv_r ts brs rs x ∈ getRAs ts brs x ∩ rs := by
    rw [renamer_inv_r, List.headD_eq_head?]
    rw [← RelationSchema.ordering_mem]
    rw [List.head?_eq_getElem?]
    rw [@List.getD_getElem?]
    split_ifs
    . simp_all
    . simp_all [Finset.ext_iff]

theorem renamer_inv_r.mem_dbs_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ rs) (h' : rs ⊆ dbs rn) :
  renamer_inv_r ts brs rs (renamer ts brs ra) ∈ dbs rn := by
    have : ra ∈ getRAs ts brs (renamer ts brs ra) := by
      refine getRAs.mem_def.mpr (And.intro (h' h) rfl)
    have := renamer_inv_r.mem_inter_def this h
    rw [getRAs] at this
    simp_all only [Finset.mem_inter, Finset.mem_filter]


theorem renamer_inv_r.mem_rs_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ rs) (h' : rs ⊆ dbs rn) :
  renamer_inv_r ts brs rs (renamer ts brs ra) ∈ rs := by
    have : ra ∈ getRAs ts brs (renamer ts brs ra) := by
      refine getRAs.mem_def.mpr (And.intro (h' h) rfl)
    have := renamer_inv_r.mem_inter_def this h
    rw [getRAs] at this
    simp_all only [Finset.mem_inter, Finset.mem_filter]

theorem renamer_inv_r.ex_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ rs) (h' : rs ⊆ dbs rn) :
  ∃k, k = renamer_inv_r ts brs rs (renamer ts brs ra) ∧ k ∈ dbs rn ∧ k ∈ rs := by
    simp_all only [exists_eq_left]
    apply And.intro
    · exact mem_dbs_def h h'
    · exact mem_rs_def h h'


def renamer_inv {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (a : String) : String :=
  (RelationSchema.ordering (getRAs ts brs a)).headD default

theorem renamer_inv.mem_inter_def (h : ra ∈ getRAs ts brs x) :
  renamer_inv ts brs x ∈ getRAs ts brs x := by
    rw [renamer_inv, List.headD_eq_head?]
    rw [← RelationSchema.ordering_mem]
    rw [List.head?_eq_getElem?]
    rw [@List.getD_getElem?]
    split
    . simp_all only [List.getElem_mem]
    . simp_all only [RelationSchema.ordering_card, Finset.card_pos,
      Finset.not_nonempty_iff_eq_empty, Finset.ext_iff, Finset.notMem_empty, iff_false,
      RelationSchema.ordering_mem]

theorem renamer_inv.mem_dbs_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  renamer_inv ts brs (renamer ts brs ra) ∈ dbs rn := by
    have : ra ∈ getRAs ts brs (renamer ts brs ra) := by
      refine getRAs.mem_def.mpr (And.intro h rfl)
    have := renamer_inv.mem_inter_def this
    rw [getRAs] at this
    simp_all only [Finset.mem_filter]

theorem renamer_inv.ex_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  ∃k, k = renamer_inv ts brs (renamer ts brs ra) ∧ k ∈ dbs rn := by
    simp_all only [exists_eq_left]
    exact mem_dbs_def h

def renamer_inv_i (i : Fin (Finset.card (getRAs ts brs a))) : String :=
  RelationSchema.fromIndex i

theorem renamer_inv_i.mem_def (i : Fin (getRAs ts brs x).card) :
  renamer_inv_i i ∈ getRAs ts brs x := by
    rw [renamer_inv_i]
    exact RelationSchema.fromIndex_mem i

theorem renamer_inv_i.mem_dbs_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (i : Fin (getRAs ts brs (renamer ts brs ra)).card) :
  renamer_inv_i i ∈ dbs rn := by
    rw [renamer_inv_i]
    apply (getRAs.mem_def.mp (RelationSchema.fromIndex_mem i)).1

theorem renamer_inv_i.ex_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  ∃i : Fin (getRAs ts brs (renamer ts brs ra)).card, renamer_inv_i i = ra := by
    simp [renamer_inv_i]
    have : ra ∈ getRAs ts brs (renamer ts brs ra) := by refine getRAs.mem_def.mpr (And.intro h rfl)
    use RelationSchema.index this
    exact RelationSchema.fromIndex_index_eq this

theorem renamer_inv_i.eq_renamer_inv_0 {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : 0 < (getRAs ts brs x).card) :
  ∃i : Fin (getRAs ts brs x).card, renamer_inv ts brs x = renamer_inv_i i := by
    use ⟨0, h⟩
    rw [renamer_inv, renamer_inv_i, RelationSchema.fromIndex]
    rw [List.headD_eq_head?_getD, Fin.cast_mk, List.get_eq_getElem]
    rw [List.head?_eq_getElem?]
    rw [@List.getD_getElem?]
    split
    . simp only
    . simp_all only [RelationSchema.ordering_card, not_true_eq_false]

theorem getRAs.card_gt_zero_def {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : a ∈ dbs rn) :
  (getRAs ts brs (renamer ts brs a)).card > 0 := by
    simp [getRAs]
    apply Finset.filter_nonempty_iff.mpr
    use a

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

-- def renamePairTuple (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : (String →. μ) → String →. μ :=
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
