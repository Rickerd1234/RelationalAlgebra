import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.ModelTheoryExtensions

open RM FOL FirstOrder Language

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : fol.BoundedFormula Attribute n :=
  q.toFormula.toPrenex

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
    simp_all only [safeDBS, iff_true, BoundedFormula.toPrenex]
  | equal =>
    simp_all only [safeDBS, iff_true, BoundedFormula.toPrenex, Term.bdEqual]
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

inductive IsPrenexT : ∀ {n}, fol.BoundedFormula α n → Type
  | of_isQF {n} {φ : fol.BoundedFormula α n} (h : BoundedFormula.IsQF φ) : IsPrenexT φ
  | all {n} {φ : fol.BoundedFormula α (n + 1)} (h : BoundedFormula.IsPrenex φ) (h' : IsPrenexT φ) : IsPrenexT φ.all
  | ex {n} {φ : fol.BoundedFormula α (n + 1)} (h : BoundedFormula.IsPrenex φ) (h' : IsPrenexT φ) : IsPrenexT φ.ex

def IsPrenexT.fold
  {n : ℕ} {φ : fol.BoundedFormula α n}
  (h : IsPrenexT φ)
  (C : ∀ {n}, fol.BoundedFormula α n → Type)
  (of_isQF : ∀ {n} {φ : fol.BoundedFormula α n}, BoundedFormula.IsQF φ → C φ)
  (all : ∀ {n} {φ : fol.BoundedFormula α (n + 1)}, BoundedFormula.IsPrenex φ → IsPrenexT φ → C φ → C φ.all)
  (ex : ∀ {n} {φ : fol.BoundedFormula α (n + 1)}, BoundedFormula.IsPrenex φ → IsPrenexT φ → C φ → C φ.ex)
  : C φ :=
  match h with
  | .of_isQF hQF    => of_isQF hQF
  | .all hP sub     => all hP sub (IsPrenexT.fold sub C of_isQF all ex)
  | .ex  hP sub     => ex  hP sub (IsPrenexT.fold sub C of_isQF all ex)

theorem IsPrenexT.toProp (h : IsPrenexT φ) : BoundedFormula.IsPrenex φ :=
  by induction h with
  | of_isQF hQF => exact BoundedFormula.IsPrenex.of_isQF hQF
  | all h ih    => exact BoundedFormula.IsPrenex.all h
  | ex h ih     => exact BoundedFormula.IsPrenex.ex h

noncomputable def IsPrenexT.fromProp
  {n : ℕ} {φ : fol.BoundedFormula α n}
  (h : BoundedFormula.IsPrenex φ) : IsPrenexT φ :=
  Classical.choice <|
    let rec aux {n} {φ : fol.BoundedFormula α n}
      (h : BoundedFormula.IsPrenex φ) :
      ∃ (_ : IsPrenexT φ), True :=
      match h with
      | .of_isQF hQF => ⟨IsPrenexT.of_isQF hQF, trivial⟩
      | .all hSub    =>
          let ⟨tSub, _⟩ := aux hSub
          ⟨IsPrenexT.all hSub tSub, trivial⟩
      | .ex hSub     =>
          let ⟨tSub, _⟩ := aux hSub
          ⟨IsPrenexT.ex hSub tSub, trivial⟩
    nonempty_of_exists (aux h)


theorem nonempty_toPrenex_IsPrenexT {φ : fol.BoundedFormula α n} : Nonempty (IsPrenexT φ.toPrenex) := by
  refine Nonempty.intro (IsPrenexT.fromProp (BoundedFormula.toPrenex_isPrenex φ))


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

theorem t (φ : fol.BoundedFormula Attribute n) : φ.IsQF → n = 0 := by
  induction φ with
  | all φ' => simp [BoundedFormula.not_all_isQF φ']
  | _ => sorry

-- theorem t (φ : fol.BoundedFormula Attribute 0) : φ.IsQF := by
--   cases φ with
--   | falsum => exact BoundedFormula.IsQF.falsum
--   | equal t₁ t₂ => exact BoundedFormula.IsAtomic.isQF (.equal t₁ t₂)
--   | rel R ts => exact BoundedFormula.IsAtomic.isQF (.rel R ts)
--   | imp => refine BoundedFormula.IsQF.imp ?_ ?_
--   | all φ' => sorry


def QFtoRA {q : fol.BoundedFormula Attribute n} (dbs : DatabaseSchema) [Fintype ↑(adomRs dbs)] (rs : RelationSchema) (h : BoundedFormula.IsQF q) : RA.Query :=
  match q with
  | _ => adom dbs rs

def toRA {q : fol.BoundedFormula Attribute n} (dbs : DatabaseSchema) [Fintype ↑(adomRs dbs)] (rs : RelationSchema) (h : IsPrenexT q) : RA.Query :=
  match h with
  | .of_isQF h' => QFtoRA dbs rs h'
  | .ex _ h' => toRA dbs rs h'
  | .all _ h' => toRA dbs rs h' -- ∀φ = ¬∃¬φ  --- (adom - (adom - toRA φ)) = toRA φ

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

theorem toRA.freeVarFinset_def (h : BoundedFormula.safeDBS φ dbs) (φ' : IsPrenexT φ) : (toRA dbs φ.freeVarFinset φ').schema dbs = φ.freeVarFinset := by
  induction φ' with
  | of_isQF => sorry
  | _ => simp_all [toRA]

@[simp]
theorem toRA.schema_def {q : FOL.Query dbs} : (toRA dbs q.schema (φ')).schema dbs = q.schema := by
  simp only [toPrenex, freeVarFinset_def, freeVarFinset_toPrenex, BoundedQuery.schema]
  have := toRA.freeVarFinset_def dbs (BoundedQuery.safeDBS q)
  sorry

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

theorem toRA.isWellTyped_def_IsPrenex {q : fol.BoundedFormula Attribute 0} (hq : q.IsPrenex) (h : BoundedFormula.safeDBS q dbs) [Fintype ↑(adomRs dbs)] :
  (toRA dbs q).isWellTyped dbs := by
    cases hq with
    | _ => unfold toRA; aesop; all_goals sorry

theorem toRA.isWellTyped_def (q : FOL.Query dbs) [Fintype ↑(adomRs dbs)] :
  (toRA dbs (toPrenex q)).isWellTyped dbs := by
    refine isWellTyped_def_IsPrenex ?_ (BoundedQuery.safeDBS_toPrenex q)
    simp [BoundedFormula.toPrenex_isPrenex]
