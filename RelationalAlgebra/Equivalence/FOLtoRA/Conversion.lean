import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.AttBuilder
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.ModelTheoryExtensions
import RelationalAlgebra.FOL.RealizeProperties

open RM FOL FirstOrder Language

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula Attribute n :=
  q.toFormula.toPrenex

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp

@[simp]
def BoundedFormula.safeR (f : fol.Relations l) (dbs : DatabaseSchema) : Prop :=
  match f with
  | FOL.relations.R dbs' rn => dbs = dbs'

@[simp]
def BoundedFormula.safeDBS (f : fol.BoundedFormula Attribute n) (dbs : DatabaseSchema) : Prop :=
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

noncomputable def TermtoAtt : fol.Term (Attribute ⊕ Fin n) → Attribute
  | var (Sum.inl a) => a
  | _ => Classical.arbitrary Attribute

@[simp]
theorem TermtoAtt.Fin0_def (t : fol.Term (Attribute ⊕ Fin 0)) : TermtoAtt t ∈ t.varFinsetLeft := by
  have ⟨k, hk⟩ := Term.cases t
  subst hk
  cases k with
  | inl a => simp_all only [Term.varFinsetLeft, Finset.mem_singleton, TermtoAtt]
  | inr a => exact Fin.elim0 a

section toRA

variable (dbs : DatabaseSchema) [Fintype (adomRs dbs)]

noncomputable def tsToRenameFunc (ts : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)) (a : Attribute) : Attribute :=
  dite (a ∈ dbs rn) (λ h => TermtoAtt (ts (RelationSchema.index h))) (λ _ => a)

noncomputable def toRA (d : ℕ) (f : fol.BoundedFormula Attribute n) (ab : AttBuilder d) : RA.Query :=
  match f with
  | .falsum => .d (adom dbs ab.schema) (adom dbs ab.schema)
  | .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (adom dbs ab.schema)
  | .rel (.R dbs rn) ts => .p ab.schema (.r (tsToRenameFunc dbs ts) (.R rn))
  | .imp f₁ f₂ => .d (adom dbs ab.schema) (.d (toRA d f₁ ab) (toRA d f₂ ab))
  | .all f => .p ab.schema (toRA (d + 1) f ab.lift)

theorem toRA.freeVarFinset_def : (toRA dbs d φ ab).schema dbs = ab.schema := by
  induction φ with
  | rel R ts =>
    cases R
    next n dbs rn =>
      simp [toRA]
  | _ => simp [toRA, adom.schema_def]

end toRA

theorem toRA.isWellTyped_def_IsAtomic {q : fol.BoundedFormula Attribute n}
  (hq : q.IsAtomic) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset ⊆ rs)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs rs q).isWellTyped dbs := by
      induction hq with
      | equal =>
        simp [Term.bdEqual, toRA, adom.isWellTyped_def]
        split_ands
        . simp [adom.schema_def]; sorry
        . simp [adom.schema_def]; sorry
      | rel R =>
        cases R with
        | R =>
          simp [Relations.boundedFormula, toRA] at h h' ⊢
          subst h
          apply And.intro
          . sorry
          . sorry

theorem toRA.isWellTyped_def_IsQF {q : fol.BoundedFormula Attribute n}
  (hq : q.IsQF) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset ⊆ rs)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs rs q).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h h'
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        have : q₁.freeVarFinset ⊆ rs := Finset.union_subset_left h'
        have : q₂.freeVarFinset ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.freeVarFinset_def]

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula Attribute n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) (h' : q.freeVarFinset ⊆ rs)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA dbs rs q).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf h h'
      | all =>
        simp [toRA, toRA.freeVarFinset_def]
        simp_all
      | ex =>
        simp at h ⊢
        simp [toRA, adom.isWellTyped_def, toRA.freeVarFinset_def, adom.schema_def]
        simp_all

theorem toRA.evalT_def_IsPrenex [folStruc dbi] {q : fol.BoundedFormula Attribute n}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbi.schema) [Fintype (adomRs dbi.schema)] :
    (toRA dbi.schema q.freeVarFinset q).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' q.freeVarFinset} := by
        induction hq with
        | _ => unfold toRA; aesop; all_goals (try simp_all [Set.diff, BoundedFormula.Realize]); all_goals sorry;


-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] : RA.Query :=
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

theorem fol_to_ra_query.evalT [folStruc dbi] [Fintype (adomRs dbi.schema)] (q : FOL.Query dbi.schema) :
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
        simp_all only [Finset.mem_coe, Pi.default_def,
          Nat.default_eq_zero, TupleToFun]
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
