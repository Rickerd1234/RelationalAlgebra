import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.FOL.Schema
import Mathlib.ModelTheory.Complexity

open RM FOL FirstOrder Language

def toPrenex (q : FOL.Query dbs) : fol.BoundedFormula Attribute 0 :=
  q.toFormula.toPrenex

noncomputable def TermtoAtt : fol.Term (Attribute ⊕ Fin 0) → Attribute
  | var (Sum.inl a) => a
  | _ => Classical.arbitrary Attribute

variable (dbs : DatabaseSchema) [Fintype ↑(adomRs dbs)] [Fintype ↑(adomAtts dbs)]

noncomputable def toRA : fol.BoundedFormula Attribute 0 → RA.Query
  | .falsum => .empty default
  | .equal t₁ t₂ => .s (TermtoAtt t₁) (TermtoAtt t₂) (adom dbs (t₁.varFinsetLeft ∪ t₂.varFinsetLeft))
  | .rel (.R dbs rn) ts => .R rn
  | .imp f₁ ⊥ => .d (adom dbs f₁.freeVarFinset) (toRA f₁)                                       --  p → ⊥  = ¬p
  | .imp (.not f₁) f₂ => .u (toRA f₁) (toRA f₂)                                                 -- ¬p → q  =  p ∨ q
  | .imp f₁ f₂ => .u (.d (adom dbs (f₁.freeVarFinset ∪ f₂.freeVarFinset)) (toRA f₁)) (toRA f₂)  --  p → q  = ¬p ∨ q
  | .all _ => .empty default

theorem toRA.schema_def {q : FOL.Query dbs} : (toRA dbs (toPrenex q)).schema dbs = q.schema := by
  cases q with
  | R rn vMap =>
    simp only [toPrenex, BoundedQuery.toFormula, fol.Rel, toRA, BoundedFormula.toPrenex, Relations.boundedFormula];
    simp;
    ext a;
    have := λ i => Term.cases (vMap i)
    simp_all [Term.varFinsetLeft]
    apply Iff.intro
    · intro a_1
      use RelationSchema.index a_1
      have ⟨k, hk⟩ := Term.cases (vMap (RelationSchema.index a_1))
      rw [hk]
      cases k with
      | inl k' =>
        simp_all only [Term.varFinsetLeft, Finset.mem_singleton]
        sorry
      | inr k' => apply Fin.elim0 k'
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨k, hk⟩ := this w
      simp [hk, Term.varFinsetLeft] at h
      subst h
      sorry
  | tEq t₁ t₂ =>
    simp [toPrenex, BoundedFormula.toPrenex, Term.bdEqual, toRA, TermtoAtt]
  | and q₁ q₂ =>
    simp [toPrenex, BoundedFormula.toPrenex, BoundedFormula.toPrenexImpRight]
    unfold BoundedFormula.toPrenexImp
    sorry
  | ex =>
    simp [toPrenex, BoundedFormula.toPrenex, BoundedFormula.toPrenexImp]
    unfold BoundedFormula.toPrenexImp
    sorry
  | or =>
    simp [toPrenex, BoundedFormula.toPrenex]
    unfold BoundedFormula.toPrenexImp
    sorry
  | not =>
    simp [toPrenex, BoundedFormula.toPrenex]
    unfold BoundedFormula.toPrenexImp
    sorry

theorem toRA.isWellTyped_def {q : FOL.Query dbs} (h : ↑q.schema ⊆ adomAtts dbs) : (toRA dbs (toPrenex q)).isWellTyped dbs := by
  cases q with
  | R => simp [toPrenex, BoundedFormula.toPrenex, Relations.boundedFormula, toRA]
  | tEq t₁ t₂ =>
    simp [toPrenex, BoundedFormula.toPrenex, Term.bdEqual, toRA, TermtoAtt]
    have := Term.cases t₁
    have := Term.cases t₂
    rename_i this_1
    simp_all only [BoundedQuery.schema.tEq_def, Sum.exists, IsEmpty.exists_iff, or_false]
    obtain ⟨w, h_1⟩ := this_1
    obtain ⟨w_1, h_2⟩ := this
    subst h_1 h_2
    simp_all only [Term.varFinsetLeft]
    apply And.intro
    · exact adom.isWellTyped_def dbs h
    · simp_all only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Finset.mem_singleton, true_or,
      or_true, and_self]
  | and q₁ q₂ =>
    simp [toPrenex, BoundedFormula.toPrenex, BoundedFormula.toPrenexImpRight]
    unfold BoundedFormula.toPrenexImp
    sorry
  | ex =>
    simp [toPrenex, BoundedFormula.toPrenex, BoundedFormula.toPrenexImp]
    unfold BoundedFormula.toPrenexImp
    sorry
  | or =>
    simp [toPrenex, BoundedFormula.toPrenex]
    unfold BoundedFormula.toPrenexImp
    sorry
  | not =>
    simp [toPrenex, BoundedFormula.toPrenex]
    unfold BoundedFormula.toPrenexImp
    sorry
