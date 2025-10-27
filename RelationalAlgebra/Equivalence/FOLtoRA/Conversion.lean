import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.ModelTheoryExtensions

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
    unfold BoundedFormula.toPrenex
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

variable (dbs : DatabaseSchema) [Fintype ↑(adomRs dbs)]

noncomputable def tsToRenameFunc (ts : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)) (a : Attribute) : Attribute :=
  dite (a ∈ dbs rn) (λ h => TermtoAtt (ts (RelationSchema.index h))) (λ _ => a)

noncomputable def toRA : RelationSchema → fol.BoundedFormula Attribute n → RA.Query
  | rs, .falsum => .d (adom dbs rs) (adom dbs rs)
  | rs, .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (adom dbs rs)
  | rs, .rel (.R dbs rn) ts => .p rs (.r (tsToRenameFunc dbs ts) (.R rn))
  | rs, .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA rs f₁) (toRA rs f₂))
  | rs, .all f => .p f.freeVarFinset (toRA rs f)

theorem toRA.freeVarFinset_def : (toRA dbs φ.freeVarFinset φ).schema dbs = φ.freeVarFinset := by
  induction φ with
  | rel R ts =>
    simp
    cases R
    next n dbs rn =>
      simp [toRA]
  | _ => simp [toRA]

end toRA

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula Attribute 0}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) [Fintype ↑(adomRs dbs)] :
    (toRA dbs q.freeVarFinset q).isWellTyped dbs := by
      cases hq with
      | _ => sorry --unfold toRA; aesop; all_goals sorry

theorem toRA.evalT_def_IsPrenex [folStruc dbi] {q : fol.BoundedFormula Attribute 0}
  (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) [Fintype ↑(adomRs dbs)] :
    (toRA dbs q.freeVarFinset q).evaluateT dbi =
      {t | ∃t' vs, BoundedFormula.Realize q t' vs ∧ t = PFun.res t' q.freeVarFinset} := by
        cases hq with
        | _ => sorry --unfold toRA; aesop; all_goals sorry


-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype ↑(adomRs dbs)] : RA.Query :=
  toRA dbs q.schema (toPrenex q)

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype ↑(adomRs dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toPrenex, toRA.freeVarFinset_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype ↑(adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex]
    refine toRA.isWellTyped_def_IsPrenex ?_ (BoundedQuery.safeDBS_toPrenex q)
    simp [BoundedFormula.toPrenex_isPrenex]

theorem fol_to_ra_query.evalT [folStruc dbi] [Fintype ↑(adomRs dbi.schema)] (q : FOL.Query dbi.schema) :
  RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q := by
    cases q with
    | _ => simp [FOL.Query.evaluateT, FOL.Query.RealizeMin.ex_def, FOL.BoundedQuery.Realize]; sorry
