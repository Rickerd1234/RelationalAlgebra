import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions

open RM FOL FirstOrder Language

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula Attribute n :=
  q.toFormula.toPrenex

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

def toRAImpRight : RA.Query → RA.Query → RA.Query
  | f₁, (.p rs sq) => .d (adom dbs (f₁.schema dbs)) f₁
  | f₁, f₂ => .u (.d (adom dbs (f₁.schema dbs ∪ f₂.schema dbs)) f₁) f₂

def toRAImp : RA.Query → RA.Query → RA.Query
  | (.d sq nq), f₂ => .u nq f₂
  | f₁,  f₂ => toRAImpRight dbs f₁ f₂

-- | .imp f₁ ⊥ => .d (adom dbs f₁.freeVarFinset) (toRA f₁)                                       --  p → ⊥  = ¬p
-- | .imp (.not f₁) f₂ => .u (toRA f₁) (toRA f₂)                                                 -- ¬p → q  =  p ∨ q
-- | .imp f₁ f₂ => .u (.d (adom dbs (f₁.freeVarFinset ∪ f₂.freeVarFinset)) (toRA f₁)) (toRA f₂)  --  p → q  = ¬p ∨ q

noncomputable def tsToRenameFunc (ts : Fin (Finset.card (dbs rn)) → fol.Term (Attribute ⊕ Fin n)) (a : Attribute) : Attribute :=
  dite (a ∈ dbs rn) (λ h => TermtoAtt (ts (RelationSchema.index h))) (λ _ => a)

noncomputable def toRA : fol.BoundedFormula Attribute n → RA.Query
  | .falsum => .p ∅ (.empty default)
  | .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (adom dbs (t₁.varFinsetLeft ∪ t₂.varFinsetLeft))
  | .rel (.R dbs rn) ts => .r (tsToRenameFunc dbs ts) (.R rn)
  | .imp f₁ f₂ => toRAImp dbs (toRA f₁) (toRA f₂)
  | .all f => .p f.freeVarFinset (.empty default)

@[simp]
theorem toRAImpRight.freeVarFinset_def
  (h₂ : q₂.isWellTyped dbs) (h₃ : q₁.schema dbs = q₂.schema dbs) :
    (toRAImpRight dbs q₁ q₂).schema dbs = q₁.schema dbs ∪ q₂.schema dbs := by
      induction q₂ with
      | _ => simp_all [toRA, toRAImp, toRAImpRight]

@[simp]
theorem toRAImp.freeVarFinset_def (h₁ : q₁.isWellTyped dbs) (h₂ : q₂.isWellTyped dbs) (h₃ : q₁.schema dbs = q₂.schema dbs) : (toRAImp dbs q₁ q₂).schema dbs = q₁.schema dbs ∪ q₂.schema dbs := by
  induction q₁ with
  | d => simp only [toRAImp]; simp_all [toRAImpRight.freeVarFinset_def dbs h₂ h₃]
  | _ => simp only [toRAImp]; simp only [toRAImpRight.freeVarFinset_def dbs h₂ h₃]

theorem toRA.freeVarFinset_def : (toRA dbs φ).schema dbs = φ.freeVarFinset := by
  induction φ with
  | rel R ts =>
    simp
    cases R
    next n dbs rn =>
      simp [toRA]
      unfold tsToRenameFunc
      simp_all [TermtoAtt]
      ext a
      simp_all only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      apply Iff.intro
      · intro a_2
        obtain ⟨w, h⟩ := a_2
        obtain ⟨left, right⟩ := h
        subst right
        split
        next h =>
          use RelationSchema.index h
          have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index h))
          simp_all [hk]
          cases k with
          | inl val => simp_all only [Term.varFinsetLeft, Finset.mem_singleton]
          | inr val_1 =>
            simp_all only [Term.varFinsetLeft, Finset.not_mem_empty]
            sorry
        next h => sorry
      · intro a_2
        obtain ⟨w, h⟩ := a_2
        sorry
  | imp f₁ f₂ ih₁ ih₂ =>
    simp [toRA];
    have h₁ : ((toRA dbs f₁).isWellTyped dbs) := by sorry
    have h₂ : ((toRA dbs f₂).isWellTyped dbs) := by sorry
    have h₃ : ((toRA dbs f₁).schema dbs) = ((toRA dbs f₂).schema dbs) := by sorry
    have := toRAImp.freeVarFinset_def dbs h₁ h₂ h₃
    convert this
    . exact id (Eq.symm ih₁)
    . exact id (Eq.symm ih₂)
  | _ => simp_all [toRA, BoundedQuery.schema]

@[simp]
theorem toRA.schema_def {q : FOL.Query dbs} : (toRA dbs (toPrenex q)).schema dbs = q.schema := by
  simp only [toPrenex, freeVarFinset_def, freeVarFinset_toPrenex, BoundedQuery.schema]

end toRA

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp

theorem toRAImpRight.isWellTyped_def {q₁ q₂ : RA.Query} [Fintype ↑(adomRs dbs)]
  (h₁ : q₁.isWellTyped dbs) (h₂ : q₂.isWellTyped dbs)
  (h₃ : q₁.schema dbs = q₂.schema dbs) :
    (toRAImpRight dbs q₁ q₂).isWellTyped dbs := by
      induction q₂ with
      | R =>
        simp_all [toRAImpRight]
        refine adom.isWellTyped_def dbs ?_
        simp [adomAtts]
        intro a
        intro h
        simp_all only [Finset.mem_coe, Set.mem_setOf_eq]
        apply Exists.intro
        · exact h
      | s =>
        simp_all [toRAImpRight]
        refine adom.isWellTyped_def dbs ?_
        simp [adomAtts]
        intro a
        intro h
        simp_all only [Finset.mem_coe, Set.mem_setOf_eq]
        sorry
      | _ =>
        simp_all [toRAImpRight]
        try (
          refine adom.isWellTyped_def dbs ?_
          simp [adomAtts]
          aesop
        )
        all_goals sorry

theorem toRAImp.isWellTyped_def  {q₁ q₂ : RA.Query} [Fintype ↑(adomRs dbs)]
  (h₁ : q₁.isWellTyped dbs) (h₂ : q₂.isWellTyped dbs)
  (h₃ : q₁.schema dbs = q₂.schema dbs) :
    (toRAImp dbs q₁ q₂).isWellTyped dbs := by
      induction q₂ with
      | _ =>
        simp_all [toRAImp]
        split
        next x x_1 sq nq => simp_all [RA.Query.isWellTyped, RA.Query.schema, and_self]
        next x x_1 x_2 x_3 => simp_all [toRAImpRight.isWellTyped_def]

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula Attribute 0} (hq : q.IsPrenex) [Fintype ↑(adomRs dbs)] :
  (toRA dbs q).isWellTyped dbs := by
    cases hq with
    | _ => unfold toRA; aesop

theorem toRA.isWellTyped_def {q : FOL.Query dbs} [Fintype ↑(adomRs dbs)] :
  (toRA dbs (toPrenex q)).isWellTyped dbs := by
    refine isWellTyped_def_IsPrenex ?_
    simp [BoundedFormula.toPrenex_isPrenex]
