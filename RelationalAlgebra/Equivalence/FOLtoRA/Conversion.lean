import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.AttBuilder
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.RealizeProperties

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

def purgeFun {n m : ℕ} : (Attribute ⊕ Fin n) →. (Attribute ⊕ Fin m) :=
  (Sum.elim (.some ∘ Sum.inl) (λ i : Fin n => dite (↑i < m) (.some ∘ Sum.inr ∘ (⟨↑i, .⟩)) (λ _ => .none)))

instance DecidablePurge (x : Attribute ⊕ Fin n) : Decidable (purgeFun (m := m) x).Dom := by
  simp [purgeFun]
  cases x with
  | inl val =>
    simp_all only [Sum.elim_inl, Function.comp_apply, Part.some_dom]
    exact instDecidableTrue
  | inr val_1 =>
    simp_all only [Sum.elim_inr]
    split
    next h =>
      simp_all only [Part.some_dom]
      exact instDecidableTrue
    next h =>
      simp_all only [not_lt, Part.not_none_dom]
      exact instDecidableFalse

@[simp]
theorem purgeFun.self_iff_eq {a : (Attribute ⊕ Fin n)} : purgeFun a = .some a := by
  simp [purgeFun]
  cases a with
  | inl val => simp_all only [Sum.elim_inl, Function.comp_apply]
  | inr val_1 => simp_all only [Sum.elim_inr]

@[simp]
theorem purgeFun.self_if_inl_def {x : (Attribute)} : purgeFun (n := n) (m := m) (Sum.inl x) = .some (Sum.inl x) := by
  rfl

@[simp]
theorem purgeFun.self_if_sub_inr_def (i : Fin n) (h : ↑i < m) : purgeFun (Attribute := Attribute) (Sum.inr i) = .some (Sum.inr (⟨i, h⟩ : Fin m)) := by
  simp [purgeFun, h]

@[simp]
theorem purgeFun.sub_if_eq_inr_def {w : Fin n} {x : Fin m} : purgeFun (Attribute := Attribute) (Sum.inr w) = Part.some (Sum.inr x) → ↑w < m := by
  simp [purgeFun]
  intro a
  split at a
  next h => simp_all only [Part.some_inj, Sum.inr.injEq]
  next h => simp_all only [not_lt, Part.none_ne_some]

@[simp]
theorem purgeFun.none_if_sup_inr_def (i : Fin n) (h : m ≤ ↑i) : purgeFun (Attribute := Attribute) (m := m) (Sum.inr i) = .none := by
  simp [purgeFun, h]

def purgeRS  [DecidableEq Attribute] (rs : Finset (Attribute ⊕ Fin n)) : Finset (Attribute ⊕ Fin m) :=
  Finset.pimage purgeFun rs

@[simp]
theorem purgeRS.self_iff_eq_def [DecidableEq Attribute] {rs : Finset (Attribute ⊕ Fin n)} : purgeRS rs = rs := by
  simp [purgeRS, Finset.pimage]

@[simp]
theorem purgeRS.id_iff_eq_def [DecidableEq Attribute] : purgeRS (m := n) (Attribute := Attribute) = id := by
  ext rs a
  simp

@[simp]
theorem purgeRS.mem_if_sub_inl_def [DecidableEq Attribute] {rs : Finset (Attribute ⊕ Fin n)} {a : Attribute} :
  (Sum.inl a) ∈ purgeRS (m := m) rs ↔ (Sum.inl a) ∈ rs := by
    simp only [purgeRS, Finset.pimage, Finset.mem_biUnion, Part.mem_toFinset, Sum.exists,
      purgeFun.self_if_inl_def, Part.mem_some_iff, Sum.inl.injEq, exists_eq_right',
      or_iff_left_iff_imp, forall_exists_index, and_imp]
    intro x_1 a_1 a_2
    rw [← Part.eq_some_iff] at a_2
    simp [purgeFun] at a_2
    split at a_2
    next h => simp_all only [Part.some_inj, reduceCtorEq]
    next h => simp_all only [not_lt, Part.none_ne_some]

@[simp]
theorem purgeRS.mem_if_sub_inr_def [DecidableEq Attribute] {rs : Finset (Attribute ⊕ Fin n)} {x : Fin m} (h : ↑x < n) :
  (Sum.inr x) ∈ purgeRS (Attribute := Attribute) rs ↔ (Sum.inr ⟨↑x, h⟩) ∈ rs := by
    simp [purgeRS, Finset.pimage]
    apply Iff.intro
    · intro a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      rw [← Part.eq_some_iff] at right
      have := purgeFun.sub_if_eq_inr_def right
      simp_all
      subst right
      simp_all only [Fin.eta]
    · intro a
      use ⟨↑x, h⟩
      simp [a]

@[simp]
theorem purgeRS.sub_if_mem_inr_def [DecidableEq Attribute] {rs : Finset (Attribute ⊕ Fin n)} {x : Fin m} :
  (Sum.inr x) ∈ purgeRS (Attribute := Attribute) rs → ↑x < n := by
    simp [purgeRS, Finset.pimage]
    intro x_1 a a_1
    rw [← Part.eq_some_iff] at a_1
    have := purgeFun.sub_if_eq_inr_def a_1
    simp_all
    subst a_1
    simp_all only [Fin.is_lt]

@[simp]
theorem purgeRS.union_def [DecidableEq Attribute] {rs rs' : Finset (Attribute ⊕ Fin n)} : purgeRS (m := m) (rs ∪ rs') = (purgeRS rs) ∪ (purgeRS rs') := Finset.pimage_union

def BoundedFormula.varFinset [DecidableEq Attribute] : (f : fol.BoundedFormula Attribute n) → Finset (Attribute ⊕ (Fin (n + BoundedFormula.depth f)))
  | .falsum => ∅
  | .rel R ts => Finset.univ.biUnion λ i => (ts i).varFinset
  | .equal t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | .imp f₁ f₂ => castLERS (varFinset f₁) (by simp) ∪ castLERS (varFinset f₂) (by simp)
  | .all f' => castLERS (varFinset f') (by simp only [depth]; grind only)

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

noncomputable def TermtoAtt : fol.Term (String ⊕ Fin n) → String ⊕ Fin n
  | var v => v
  | _ => Sum.inl (Classical.arbitrary String)

section toRA

variable (dbs : String → Finset String) [Fintype (adomRs dbs)]

noncomputable def tsToRenameFunc (ts : Fin (Finset.card (dbs rn)) → fol.Term (String ⊕ Fin n)) (a : String ⊕ Fin n) : String ⊕ Fin n :=
  a.elim (λ s => dite (s ∈ dbs rn) (λ h => TermtoAtt (ts (RelationSchema.index h))) (λ _ => a)) (λ _ => a)

def filterLast : (String ⊕ Fin (n + 1)) → Prop := (Sum.elim (λ _ => True) (λ v => v ≠ Fin.last n))

@[simp]
theorem filterLast.inl_def : filterLast (n := n) (Sum.inl a) = True := rfl

@[simp]
theorem filterLast.inr_def_ne_last {v : Fin (n + 1)} (h : v ≠ Fin.last n) : filterLast (Sum.inr v) = True := by
  simp [filterLast, h]

@[simp]
theorem filterLast.inr_def_eq_last {v : Fin (n + 1)} (h : v = Fin.last n) : filterLast (Sum.inr v) = False := by
  simp [filterLast, h]

instance DecidableFilterLast :
  DecidablePred (α := String ⊕ Fin (n + 1)) filterLast := by
  intro a
  cases a with
  | inl val =>
    simp_all only [filterLast, ne_eq, Sum.elim_inl]
    exact instDecidableTrue
  | inr val_1 =>
    simp_all only [filterLast, ne_eq, Sum.elim_inr]
    exact instDecidableNot

@[simp]
theorem filterLast.mem_inl_def {rs : Finset (String ⊕ Fin (n + 1))} : (Sum.inl x) ∈ rs.filter filterLast ↔ (Sum.inl x) ∈ rs := by simp

@[simp]
theorem filterLast.mem_inr_def {rs : Finset (String ⊕ Fin (n + 1))} : (Sum.inr v) ∈ rs.filter filterLast ↔ v ≠ Fin.last n ∧ Sum.inr v ∈ rs := by
  rw [@Finset.mem_filter, ne_eq]
  by_cases h : v = Fin.last n
  . simp_all only [inr_def_eq_last, and_false, not_true_eq_false, false_and]
  . simp_all only [filterLast.inr_def_ne_last h, and_true, not_false_eq_true, true_and]

noncomputable def castPredSum {n} : (String ⊕ Fin (n + 1)) → (String ⊕ Fin n) :=
  Sum.elim (Sum.inl) (λ v => dite (v = Fin.last n) (λ _ => Sum.inl (Classical.arbitrary String)) (Sum.inr ∘ v.castPred))

@[simp]
theorem castFilterLast.inl_def : castPredSum (n := n) (Sum.inl a) = Sum.inl a := rfl

@[simp]
theorem castFilterLast.inr_def_ne_last {v : Fin (n + 1)} (h : v ≠ Fin.last n) : castPredSum (Sum.inr v) = (Sum.inr (v.castPred h)) := by
  simp [castPredSum, h]

@[simp]
theorem castFilterLast.inr_def_eq_last {v : Fin (n + 1)} (h : v = Fin.last n) : castPredSum (Sum.inr v) = Sum.inl (Classical.arbitrary String) := by
  simp [castPredSum, h]

noncomputable def forgetLast (rs : Finset (String ⊕ Fin (n + 1))) : Finset (String ⊕ Fin n) :=
  (rs.filter filterLast).image castPredSum

@[simp]
theorem forgetLast.ext_iff_inl : Sum.inl x ∈ forgetLast rs ↔ Sum.inl x ∈ rs := by
  simp_all [forgetLast]
  intro x_1 a_1 a_2 a_3
  rename_i n
  by_cases x_1 = Fin.last n
  . simp_all
  . simp_all

@[simp]
theorem forgetLast.ext_iff_inr {rs : Finset (String ⊕ Fin (n + 1))} : Sum.inr x ∈ forgetLast rs ↔ Sum.inr x.castSucc ∈ rs ∧ x.castSucc ≠ Fin.last n := by
  simp_all [forgetLast]
  by_cases hc : x.castSucc = Fin.last n
  . simp_all
  . apply Iff.intro
    . intro h
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      rw [castFilterLast.inr_def_ne_last right_1] at right
      simp [← Sum.inr_injective right, left]
    . simp_all
      intro a
      use x.castSucc
      simp_all only [ne_eq, Fin.castSucc_ne_last, not_false_eq_true, filterLast.inr_def_ne_last, and_self,
        castFilterLast.inr_def_ne_last, Fin.castPred_castSucc]

noncomputable def castPredQ : RA.Query String (String ⊕ Fin (n + 1)) → RA.Query String (String ⊕ Fin n)
  | .R rn => .R rn
  | .s a b q => .s (castPredSum a) (castPredSum b) (castPredQ q)
  | .p rs q => .p (rs.image castPredSum) (castPredQ q)
  | .j q₁ q₂ => .j (castPredQ q₁) (castPredQ q₂)
  | .r f q => .r (λ a => (f (a.map id Fin.castSucc)).elim (Sum.inl) (castPredSum ∘ Sum.inr)) (castPredQ q)
  | .d q nq => .d (castPredQ q) (castPredQ nq)
  | .u q₁ q₂ => .u (castPredQ q₁) (castPredQ q₂)

def castLESum (h : n ≤ m) : String ⊕ Fin n  → String ⊕ Fin m :=
  Sum.map id (Fin.castLE h)

@[simp]
theorem castLESum.self_id_def (h : n ≤ n) : castLESum h = id := by simp [castLESum]

@[simp]
theorem castLESum.lt_def {h : n ≤ m} : castLESum h a = a.map id (Fin.castLE h) := by simp [castLESum]

noncomputable def castLEQ (h : n ≤ m) : RA.Query String (String ⊕ Fin n) → RA.Query String (String ⊕ Fin m)
  | .R rn => .R rn
  | .s a b q => .s (castLESum h a) (castLESum h b) (castLEQ h q)
  | .p rs q => .p (rs.image (castLESum h)) (castLEQ h q)
  | .j q₁ q₂ => .j (castLEQ h q₁) (castLEQ h q₂)
  | .r f q => .r (λ a => ((a.elim (castLESum h ∘ f ∘ Sum.inl) (λ i : Fin m => dite (↑i < n) (λ h' => (castLESum h (f (Sum.inr ⟨i, h'⟩)))) (λ _ => Sum.inr ↑i))))) (castLEQ h q)
  | .d q nq => .d (castLEQ h q) (castLEQ h nq)
  | .u q₁ q₂ => .u (castLEQ h q₁) (castLEQ h q₂)

@[simp]
theorem castLEQ.eq_schema_def {dbs : String → Finset (String ⊕ Fin n)} {h : n ≤ n} : (castLEQ h q).schema dbs = q.schema dbs := by
  induction q with
  | r =>
    simp [castLEQ]
    simp_all
    ext a
    simp_all only [Finset.mem_image, Sum.exists, Sum.elim_inl, Function.comp_apply, Sum.elim_inr]
  | _ => simp [castLEQ]; try simp_all only

@[simp]
theorem castLEQ.lt_schema_def {dbs : String → Finset (String ⊕ Fin m)} {h : n < m} : purgeRS ((castLEQ h q).schema dbs) = q.schema (purgeRS ∘ dbs) := by
  induction q with
  | p =>
    simp [castLEQ, purgeRS, purgeFun, castLESum]
    simp_all only [Nat.succ_eq_add_one, Function.comp_apply]
    ext a_2 : 1
    simp_all only [Function.comp_apply, Finset.mem_pimage, Finset.mem_image, Sum.exists, Sum.map_inl, id_eq,
      Sum.map_inr, Sum.inl.injEq, exists_eq_right, reduceCtorEq, and_false, exists_const, or_false, Sum.elim_inl,
      Part.mem_some_iff, Sum.inr.injEq, false_or, Sum.elim_inr, exists_exists_and_eq_and, Fin.coe_castLE, Fin.is_lt,
      ↓reduceDIte, Fin.eta]
    cases a_2 with
    | inl val => simp_all only [Sum.inl.injEq, exists_eq_right', reduceCtorEq, and_false, exists_const, or_false]
    | inr val_1 => simp_all only [reduceCtorEq, and_false, exists_const, Sum.inr.injEq, exists_eq_right', false_or]
  | j q₁ q₂ ih₁ ih₂ =>
    simp [castLEQ]
    rw [← ih₁, ← ih₂]
  | r =>
    simp [castLEQ]
    simp_all
    ext a
    sorry
  | _ => simp [castLEQ]; try simp_all only

variable [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]

instance : Nonempty (String ⊕ Fin n) := by exact Sum.nonemptyLeft

@[simp]
noncomputable def convAdom (rs : Finset (String ⊕ Fin n)) : RA.Query String (String ⊕ Fin n) := adom ((Finset.image Sum.inl) ∘ dbs) rs

noncomputable def allToRA
    (q' : RA.Query String (String ⊕ Fin (n + m + 1))) (rs : Finset (String ⊕ Fin (n + m + 1))) : RA.Query String (String ⊕ Fin (n + m + 1)) :=
      (convAdom dbs (purgeRS rs)).d (.p (purgeRS rs) q')

theorem allToRA.schema_def :
    (allToRA dbs φ rs).schema ((Finset.image Sum.inl) ∘ dbs) = purgeRS rs := by
  induction φ with
  | R =>
    simp [allToRA]
    exact adom.schema_def
  | _ => expose_names; exact a_ih

theorem castAllEq : n +  BoundedFormula.depth f' + 1 =  n + BoundedFormula.depth (∀'f') := by simp; grind;
theorem castAllLE : n +  BoundedFormula.depth f' + 1 ≤  n + BoundedFormula.depth (∀'f') := by simp; grind;

noncomputable def toRA
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]
  (f : fol.BoundedFormula String n) (rs : Finset (String ⊕ Fin ((n + BoundedFormula.depth f)))) : RA.Query String (String ⊕ Fin (n + BoundedFormula.depth f)) :=
    match f with
    | .falsum => .d (convAdom dbs rs) (convAdom dbs rs)
    | .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (convAdom dbs rs)
    | .rel (.R dbs' rn) ts => .p rs (.j (convAdom dbs rs) (.r (tsToRenameFunc dbs' ts) (.R rn)))
    | .imp f₁ f₂ => .d (convAdom dbs rs) (.d (castLEQ (by simp) (toRA f₁ (purgeRS rs))) (castLEQ (by simp) (toRA f₂ (purgeRS rs))))
    | .all f' => castLEQ castAllLE (allToRA (n := n) (m := BoundedFormula.depth f') dbs (castLEQ (by grind) (toRA f' (purgeRS rs))) (purgeRS rs))

theorem toRA.schema_def [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] {rs : Finset (String ⊕ Fin n)} :
    (toRA dbs φ (BoundedFormula.varFinset φ)).schema ((Finset.image Sum.inl) ∘ dbs) = (BoundedFormula.varFinset φ) := by
  induction φ with
  | rel R ts =>
    cases R
    next n dbs rn =>
      simp [toRA]
  | all =>
    simp [toRA]
    apply allToRA.schema_def dbs
  | _ => simp [toRA, adom.schema_def, BoundedFormula.varFinset, purgeRS]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : fol.BoundedFormula String n}
  (hq : q.IsAtomic) (h : BoundedFormula.safeDBS q dbs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs q (BoundedFormula.varFinset q)).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, adom.isWellTyped_def]
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂
        -- simp [TermToAtt]
        -- rw [Term.bdEqual, BoundedFormula.freeVarFinset, Finset.image_subset_iff, Term.varFinsetLeft.eq_def] at h'
        split_ands
        all_goals(
          simp [adom.schema_def, TermtoAtt, BoundedFormula.varFinset]
        )
      | rel R ts =>
        cases R with
        | R dbs rn =>
          simp [Relations.boundedFormula, toRA] at h ⊢
          subst h
          apply And.intro
          . apply And.intro
            . exact adom.isWellTyped_def
            . sorry
          . rw [Finset.subset_iff]
            rename_i inst_7
            intro x a
            simp_all [nonempty_subtype, Finset.mem_image, exists_exists_and_eq_and, BoundedFormula.varFinset, adom.schema_def]

theorem toRA.isWellTyped_def_IsQF {q : fol.BoundedFormula String n}
  (hq : q.IsQF) (h : BoundedFormula.safeDBS q dbs) --(h' : q.freeVarFinset.image Sum.inl ⊆ rs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)] [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))]:
    (toRA dbs q (BoundedFormula.varFinset q)).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        -- simp [Finset.image_union q₁.freeVarFinset q₂.freeVarFinset] at h'
        -- have : q₁.freeVarFinset.image Sum.inl ⊆ rs := Finset.union_subset_left h'
        -- have : q₂.freeVarFinset.image Sum.inl ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]
        rename_i inst_6 inst_7
        obtain ⟨w, h_1⟩ := inst_6
        obtain ⟨left, right⟩ := h
        apply And.intro
        · apply And.intro
          · sorry
          · apply And.intro
            · sorry
            · sorry
        · sorry

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) --(h' : q.freeVarFinset.image Sum.inl ⊆ rs)
  [∀n, DecidableRel (α := String ⊕ Fin n) (.≤.)] [∀n, IsTrans (String ⊕ Fin n) (.≤.)] [∀n, IsAntisymm (String ⊕ Fin n) (.≤.)] [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)]
  [∀n, IsTotal (String ⊕ Fin n) (.≤.)] [∀n, Fintype (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] [∀n, Nonempty (adomRs (α := String ⊕ Fin n) ((Finset.image Sum.inl) ∘ dbs))] :
    (toRA dbs q (BoundedFormula.varFinset q)).isWellTyped ((Finset.image Sum.inl) ∘ dbs) := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf h
      | all =>
        simp [toRA, toRA.schema_def]
        simp_all
      | ex =>
        simp at h ⊢
        simp [toRA, adom.isWellTyped_def, toRA.schema_def, adom.schema_def]
        simp_all

theorem toRA.evalT_def_IsPrenex [folStruc dbi (μ := μ)] {q : fol.BoundedFormula String n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbi.schema) [Fintype (adomRs dbi.schema)] :
    (toRA dbi.schema q.freeVarFinset q).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' q.freeVarFinset} := by
        induction hq with
        | _ => sorry --unfold toRA; aesop; all_goals (try simp_all [Set.diff, BoundedFormula.Realize]); all_goals sorry;


-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query String String :=
  toRA dbs q.schema (toPrenex q)

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.freeVarFinset_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex]
    refine toRA.isWellTyped_def_IsPrenex ?_ (BoundedQuery.safeDBS_toPrenex q) ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp

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
