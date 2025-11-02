import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.AttBuilder
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.RealizeProperties
import Mathlib.Data.Finset.Fin
import Cslib.Foundations.Data.HasFresh

open RM FOL FirstOrder Language

variable {μ : Type}

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula String n :=
  q.toFormula.toPrenex

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp

@[simp]
def BoundedFormula.depth : fol.BoundedFormula Attribute n → ℕ
  | .falsum => 0
  | .rel _ _ => 0
  | .equal _ _ => 0
  | .imp f₁ f₂ => max (depth f₁) (depth f₂)
  | .all f' => 1 + depth f'

def castLERS  [DecidableEq Attribute] (rs : Finset (Attribute ⊕ Fin n)) (h : n ≤ m) : Finset (Attribute ⊕ Fin m) :=
  Finset.image (Sum.map id (Fin.castLE h)) rs

@[simp]
def BoundedFormula.varFinset [DecidableEq Attribute] : (f : fol.BoundedFormula Attribute n) → Finset (Attribute ⊕ (Fin (n + BoundedFormula.depth f)))
  | .falsum => ∅
  | .rel R ts => Finset.univ.biUnion λ i => (ts i).varFinset
  | .equal t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | .imp f₁ f₂ => castLERS (varFinset f₁) (by simp) ∪ castLERS (varFinset f₂) (by simp)
  | .all f' => castLERS (varFinset f') (by simp only [depth]; grind only)

-- def ex_dbs : String → Finset String
--   | "R1" => {"a", "b", "c"}
--   | "R2" => {"d", "e", "f"}
--   | "R3" => {"a", "b", "d"}
--   | _ => ∅

-- #simp [BoundedFormula.varFinset] BoundedFormula.varFinset (.falsum (α := String) (n := 0))
-- #simp [BoundedFormula.varFinset] BoundedFormula.varFinset (.rel (.R ex_dbs "R2") ([outVar "b", outVar "c", inVar 0].get) (α := String) (n := 1))
-- #simp [BoundedFormula.varFinset] BoundedFormula.varFinset (.equal (outVar "a") (inVar 0) (n := 1))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.imp (.equal (outVar "a") (inVar 0)) (.equal (outVar "b") (inVar 1)) (n := 2))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.all (.equal (outVar "a") (inVar 0)) (n := 0))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.all (.imp (.all (.equal (outVar "a") (inVar 1))) (.all (.equal (outVar "b") (inVar 1)))) (n := 0))

@[simp]
def toDot (n : ℕ) : String := n.fold (λ _ _ p ↦ p ++ ".") ""

@[simp]
theorem toDot.length (n : ℕ) : (toDot n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>  rw [toDot, Nat.fold_succ, String.length_append, ← toDot, ih, Nat.add_left_cancel_iff]; rfl

@[simp]
theorem toDot.length' (n m : ℕ) : (toDot n).length = m ↔ m = n := by
  induction m with
  | zero => rw [toDot.length (n := n)]; grind
  | succ n ih =>  rw [toDot.length]; grind

theorem toDot.inj : (toDot).Injective := by
  intro a₁ a₂ h
  let h' := toDot.length a₁
  rw [h, toDot.length' a₂ a₁] at h'
  exact h'

@[simp]
def emb : ℕ ↪ String := ⟨toDot, toDot.inj⟩

@[simp]
def BoundedFormula.safeR (f : fol.Relations l) (dbs : String → Finset String) : Prop :=
  match f with
  | FOL.relations.R dbs' rn => dbs = dbs'

@[simp]
def BoundedFormula.safeDBS (f : fol.BoundedFormula Attribute n) (dbs : String → Finset String) : Prop :=
  match f with
  | .falsum => True
  | .rel R _ => safeR R dbs
  | .equal _ _ => True
  | .imp f₁ f₂ => safeDBS f₁ dbs ∧ safeDBS f₂ dbs
  | .all f' => safeDBS f' dbs

@[simp]
theorem BoundedFormula.safeDBS_ToPrenex (q : fol.BoundedFormula Attribute n) : BoundedFormula.safeDBS q.toPrenex dbs ↔ BoundedFormula.safeDBS q dbs := by
  induction q with
  | falsum =>
    simp_all only [safeDBS, BoundedFormula.toPrenex]
  | equal =>
    simp_all only [safeDBS, BoundedFormula.toPrenex, Term.bdEqual]
  | imp =>
    simp_all only [safeDBS]
    simp [BoundedFormula.toPrenex]
    sorry
  | _ => aesop

@[simp]
theorem BoundedQuery.safeDBS (q : FOL.BoundedQuery dbs n) : BoundedFormula.safeDBS q.toFormula dbs := by
  induction q with
  | _ => aesop

@[simp]
theorem BoundedQuery.safeDBS_toPrenex (q : FOL.BoundedQuery dbs n) : BoundedFormula.safeDBS q.toFormula.toPrenex dbs := by
  simp_all only [BoundedFormula.safeDBS_ToPrenex, safeDBS]

noncomputable def TermtoAtt (f : (Fin n → String)) : fol.Term (String ⊕ Fin n) → String
  | var (Sum.inl s) => s
  | var (Sum.inr i) => f i
  | _ => Classical.arbitrary String

section toRA

def FRanS (f : Fin n → String) : Set String := {a | ∃i, f i = a}

instance FRanSFin {f : Fin n → String} : Fintype (FRanS f) := by
  apply Fintype.ofFinset (((Finset.range n).attachFin (by intro n h; simp at h; apply h)).image f)
  . simp [FRanS]

def FRan (f : Fin n → String) : Finset String := (FRanS f).toFinset

def FRan.default := FRan Fin.elim0

@[simp]
theorem FRan.default_eq_empty : FRan.default = ∅ := by simp [default, FRan, FRanS]

noncomputable def liftF (f' : Fin n → String) (brs : Finset String) : Fin (n + 1) → String :=
  Fin.snoc f' ((RelationSchema.ordering brs).getD n (Classical.arbitrary String))

@[simp]
theorem FRan.liftF_sub {f : Fin n → String} : FRan f ⊆ FRan (liftF f brs) := by
  simp [FRan, FRanS, liftF]
  intro i
  use i.castLE (Nat.le_add_right n 1)
  simp_all [Fin.snoc]
  rfl

@[simp]
theorem FRan.liftF_union {f : Fin n → String} : FRan f ∪ FRan (liftF f brs) = FRan (liftF f brs) := Finset.union_eq_right.mpr liftF_sub

@[simp]
theorem FRan.liftF_sub_brs {f : Fin n → String} (h : n < brs.card) (h' : FRan f ⊆ brs) : FRan (liftF f brs) ⊆ brs := by
  simp [FRan, FRanS, liftF] at h' ⊢
  intro i h
  obtain ⟨w, h⟩ := h
  subst h
  by_cases hc : w = Fin.last n
  . subst hc
    simp
    rw [← RelationSchema.ordering_mem, @List.getD_getElem?]
    simp [h]
  . have : ↑w < n := Fin.lt_last_iff_ne_last.mpr hc
    simp [Fin.snoc, this]
    simp [Set.subset_def] at h'
    simp [h']

@[simp]
theorem FRan.liftF_union_brs {f : Fin n → String} (h : n < brs.card) (h' : FRan f ⊆ brs) : (brs ∪ FRan (liftF f brs)) = brs := Finset.union_eq_left.mpr (liftF_sub_brs h h')

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def tsToRenameFunc (f : Fin n → String) (ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)) (a : String) : String :=
  dite (a ∈ dbs rn) (λ h => TermtoAtt f (ts (RelationSchema.index h))) (λ _ => a)

theorem tsToRenameFunc.injective {ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)} (h : (Finset.univ.biUnion λ i => (ts i).varFinsetLeft) ∩ (FRan f) = ∅) :
  Function.Injective (tsToRenameFunc dbs f ts) := by
    simp [Function.Injective, tsToRenameFunc, TermtoAtt]
    sorry


theorem tsToRenameFunc.surjective {ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)} (h : (Finset.univ.biUnion λ i => (ts i).varFinsetLeft) ∩ (FRan f) = ∅) :
  Function.Surjective (tsToRenameFunc dbs f ts) := by
    simp [Function.Surjective, tsToRenameFunc]
    intro b
    use b
    sorry

theorem tsToRenameFunc.bijective {ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)} (h : (Finset.univ.biUnion λ i => (ts i).varFinsetLeft) ∩ (FRan f) = ∅) :
  Function.Bijective (tsToRenameFunc dbs f ts) :=
    ⟨tsToRenameFunc.injective dbs h, tsToRenameFunc.surjective dbs h⟩

noncomputable def allToRA (q' : RA.Query String String) (f : Fin n → String) (rs : Finset String) : RA.Query String String :=
  (adom dbs rs).d (.p rs q')

theorem allToRA.schema_def : (allToRA dbs q f rs).schema dbs = rs := by
  induction q with
  | R =>
    simp [allToRA]
    exact adom.schema_def
  | _ => expose_names; exact a_ih

theorem allToRA.isWellTyped_def (h : q.isWellTyped dbs) (f : Fin n → String) (h' : q.schema dbs = rs) [Nonempty ↑(adomRs dbs)] :
  (allToRA dbs q f rs).isWellTyped dbs := by
    simp [allToRA]
    simp_all only [nonempty_subtype, subset_refl, and_self, adom.isWellTyped_def, adom.schema_def]

noncomputable def toRA
  (f : fol.BoundedFormula String n) (f' : Fin n → String) (rs brs : Finset String) : RA.Query String String :=
    match f with
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt f' t₁) (TermtoAtt f' t₂) (adom dbs rs)
    | .rel (.R dbs' rn) ts => .p rs (.j (adom dbs rs) (.r (tsToRenameFunc dbs' f' ts) (.R rn)))
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ f' rs brs) (toRA f₂ f' rs brs))
    | .all sf => allToRA dbs (toRA sf (liftF f' brs) (rs ∪ FRan (liftF f' brs)) brs) f' rs

theorem toRA.schema_def :
    (toRA dbs φ f rs brs).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n dbs rn =>
      simp [toRA]
  | all =>
    simp [toRA]
    apply allToRA.schema_def dbs
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : fol.BoundedFormula String n}
  (hq : q.IsAtomic) (h : BoundedFormula.safeDBS q dbs) (f : Fin n → String) (h' : (q.freeVarFinset ∪ FRan f) ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (h''' : FRan f ⊆ brs)
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
          simp [Term.bdEqual] at h' h''
          simp [adom.schema_def, TermtoAtt]
          rename_i inst_1
          simp_all only [nonempty_subtype]
          obtain ⟨w, h_1⟩ := inst_1
          cases k₁ with
          | inl val =>
            cases k₂ with
            | inl
              val_1 =>
              simp_all only [Term.varFinsetLeft, Finset.union_singleton, Finset.singleton_union, Finset.union_insert]
              grind
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.union_empty, Finset.empty_union, Finset.singleton_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
          | inr val_1 =>
            cases k₂ with
            | inl
              val =>
              simp_all only [Term.varFinsetLeft, Finset.union_singleton, insert_empty_eq, Finset.singleton_union,
                Finset.union_insert, Finset.empty_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.union_idempotent, Finset.empty_inter, Finset.empty_union]
              simp [FRan, FRanS] at *
              try simp_all [Set.subset_def]
        )
      | rel R ts =>
        cases R with
        | R dbs rn =>
          simp [Relations.boundedFormula, toRA] at h h' h'' ⊢
          subst h
          apply And.intro
          . apply And.intro
            . exact adom.isWellTyped_def
            . exact tsToRenameFunc.bijective dbs (by grind)
          . rw [Finset.subset_iff]
            rename_i inst_7
            intro x a
            simp_all [nonempty_subtype, Finset.mem_image, adom.schema_def]

theorem toRA.isWellTyped_def_IsQF [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] {q : fol.BoundedFormula String n}
  (hq : q.IsQF) (h : BoundedFormula.safeDBS q dbs) (f : Fin n → String) (h' : (q.freeVarFinset ∪ FRan f) ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (h''' : FRan f ⊆ brs) :
    (toRA dbs q f rs brs).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h f h' h'' h'''
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp only [RA.Query.isWellTyped, RA.Query.schema]
        simp at h'
        have : q₁.freeVarFinset ∪ FRan f ⊆ rs := by grind
        have : q₂.freeVarFinset ∪ FRan f ⊆ rs := Finset.union_subset_right h'
        have : q₁.freeVarFinset ∩ brs = ∅ := by simp at h''; grind
        have : q₂.freeVarFinset ∩ brs = ∅ := by simp at h''; grind
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) (h' : (q.freeVarFinset ∪ brs) ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (h''' : FRan f ⊆ brs) (h'''' : brs.card > n + BoundedFormula.depth q)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q f (rs ∪ FRan f) brs).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf h f (by grind) h'' h'''
      | all =>
        simp at h ⊢
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        . apply allToRA.isWellTyped_def dbs ?_ f ?_
          . refine h_ih (f := (liftF f brs)) ?_ ?_ ?_ ?_ ?_
            . simp_all
            . simp_all
            . simp_all
            . exact FRan.liftF_sub_brs (by grind) h'''
            . simp at h''''; grind
          . simp_all [schema_def dbs]
            ext a
            simp
            have := FRan.liftF_sub_brs (f := f) (by grind) h'''
            apply Iff.intro
            . grind
            . grind

      | ex =>
        simp at h ⊢
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp only [adom.isWellTyped_def, true_and, *]
        apply And.intro
        · apply And.intro
          · apply allToRA.isWellTyped_def
            . simp_all only [gt_iff_lt,
              BoundedFormula.depth, zero_le,
              sup_of_le_left, RA.Query.isWellTyped, adom.isWellTyped_def, adom.schema_def, and_self,
              schema_def, RA.Query.schema, and_true, true_and]
              . apply h_ih
                . grind
                . simp_all
                . simp_all
                . exact FRan.liftF_sub_brs (by grind) h'''
                . grind
            . simp_all [adom.schema_def]
              ext a
              simp
              have := FRan.liftF_sub_brs (f := f) (by grind) h'''
              apply Iff.intro
              . grind
              . grind
          · rfl
        · rfl

theorem toRA.evalT_def_IsPrenex [folStruc dbi (μ := μ)] {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbi.schema) [Fintype (adomRs dbi.schema)] :
    (toRA dbi.schema q f (q.freeVarFinset ∪ brs) brs).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' q.freeVarFinset} := by
        induction hq with
        | _ => sorry --unfold toRA; aesop; all_goals (try simp_all [Set.diff, BoundedFormula.Realize]); all_goals sorry;


@[simp]
def freshStringsS (n : ℕ) : Set String := {a | ∃i ∈ (Finset.range n), toString i = a}

instance freshStringsSFin : Fintype (freshStringsS n) := by
  apply Fintype.ofFinset (((Finset.range n).attachFin (by intro n h; simp at h; apply h)).image (toString ∘ Fin.val))
  . simp
    intro s
    apply Iff.intro
    . intro ⟨a, ha⟩
      use a
      simp [ha]
    . intro ⟨a, ha, ha'⟩
      use ⟨a, ha⟩

@[simp]
def freshStrings (n : ℕ) : Finset String := (freshStringsS n).toFinset

theorem freshString.card_def : (freshStrings n).card = n := by
  simp;
  rw [Fintype.card];
  induction n;
  . simp_all only [Finset.range_zero, Finset.card_univ, Finset.notMem_empty, false_and, exists_const]
    rfl
  . simp_all only [Finset.card_univ, Finset.mem_range]
    HasFresh

@[simp]
def getBRS (f : fol.BoundedFormula String n) :=
  (freshStrings (n + BoundedFormula.depth f)) \ f.freeVarFinset



-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs (toPrenex q) (Fin.elim0) q.schema (getBRS q)

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.schema_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan.default = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, ← this]
    refine toRA.isWellTyped_def_IsPrenex ?_ (BoundedQuery.safeDBS_toPrenex q) ?_ ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp [FRan, FRanS]
    . simp [FRan, FRanS]

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Nonempty μ] (q : FOL.Query dbi.schema) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q := by
    rw [FOL.Query.evaluateT, Set.ext_iff]
    intro t
    rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
    rw [fol_to_ra_query, BoundedQuery.schema, toPrenex]
    have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
    have h_safe := BoundedQuery.safeDBS_toPrenex q
    rw [← freeVarFinset_toPrenex, toRA.evalT_def_IsPrenex hq h_safe]
    rw [Set.mem_setOf_eq]
    simp only [BoundedFormula.realize_toPrenex]
    simp_all only [BoundedFormula.safeDBS_ToPrenex, BoundedQuery.safeDBS, freeVarFinset_toPrenex,
      exists_and_right]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      refine Exists.intro rfl ?_
      rw [← BoundedQuery.Realize] at left ⊢
      obtain ⟨vs, left⟩ := left
      have : vs = default := by ext v; exact False.elim (Fin.elim0 v)
      subst this
      refine (BoundedQuery.Realize.restrict ?_ ?_).mp left
      . rw [freeVarFinset_toPrenex]
      . rw [freeVarFinset_toPrenex, BoundedQuery.schema]
    · intro a
      obtain ⟨w, h⟩ := a
      use TupleToFun w
      apply And.intro ?_
      . ext a v
        rw [PFun.mem_res]
        simp_all only [Finset.mem_coe, TupleToFun]
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
          rw [← w a] at left
          simp [Part.getOrElse, left, Part.get_mem]
      . use default
        rw [← BoundedQuery.Realize] at h ⊢
        have : ∀x x' t, x = x' → (q.Realize dbi x t → q.Realize dbi x' t) := by simp
        apply (this (TupleToFun ?_) (TupleToFun w) default ?_) h
        . simp [w]
        . simp [w]
