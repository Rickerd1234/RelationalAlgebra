import RelationalAlgebra.Equivalence.RAtoFOL.Relation
import RelationalAlgebra.Equivalence.RAtoFOL.Selection
import RelationalAlgebra.Equivalence.RAtoFOL.Projection
import RelationalAlgebra.Equivalence.RAtoFOL.Join
import RelationalAlgebra.Equivalence.RAtoFOL.Rename
import RelationalAlgebra.Equivalence.RAtoFOL.Union
import RelationalAlgebra.Equivalence.RAtoFOL.Diff
import RelationalAlgebra.Equivalence.FOLtoRA.Conversion
import RelationalAlgebra.Equivalence.FOLtoRA.EvaluateAdom

open RM

section RAtoFOL

variable {dbi : DatabaseInstance _ _ _} [FOL.folStruc dbi (μ := μ)] [Nonempty μ] (raQ : RA.Query String String) (h : RA.Query.isWellTyped dbi.schema raQ)

theorem ra_to_fol_evalT (h : RA.Query.isWellTyped dbi.schema raQ) :
  (ra_to_fol_query dbi.schema raQ).evaluateT dbi = RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn => exact ra_to_fol_evalT.R_def_eq h
    | s a b sq ih => exact ra_to_fol_evalT.s_def_eq h (ih h.1)
    | p rs sq ih => exact ra_to_fol_evalT.p_def_eq h (ih h.1)
    | j q₁ q₂ ih₁ ih₂ => exact ra_to_fol_evalT.j_def_eq h (ih₁ h.1) (ih₂ h.2)
    | r f q ih => exact ra_to_fol_evalT.r_def_eq h (ih h.1)
    | u q₁ q₂ ih₁ ih₂ => exact ra_to_fol_evalT.u_def_eq h (ih₁ h.1) (ih₂ h.2.1)
    | d q nq ih nih => exact ra_to_fol_evalT.d_def_eq h (ih h.1) (nih h.2.1)

theorem ra_to_fol_eval :
  (ra_to_fol_query dbi.schema raQ).evaluate dbi = raQ.evaluate dbi h := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    simp_all [ra_to_fol_query_schema]
    exact ra_to_fol_evalT raQ h

theorem ra_to_fol :
  ∃folQ : FOL.Query dbi.schema, folQ.evaluate dbi = raQ.evaluate dbi h := by
    use ra_to_fol_query dbi.schema raQ
    exact ra_to_fol_eval raQ h

end RAtoFOL

section FOLtoRA

variable {dbi _ _ _} [FOL.folStruc dbi (μ := μ)] [Nonempty μ] [Fintype (adomRs dbi.schema)] [Nonempty (adomRs dbi.schema)] (folQ : FOL.Query dbi.schema)

theorem fol_to_ra_eval (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema (FreshAtts (toPrenex folQ)) (FOL.BoundedQuery.toFormula folQ)) :
  (fol_to_ra_query folQ).evaluate dbi (fol_to_ra_query.isWellTyped_def folQ) = folQ.evaluateAdom dbi := by
    simp only [RA.Query.evaluate, FOL.Query.evaluateAdom, RelationInstance.mk.injEq]
    apply And.intro
    · exact fol_to_ra_query.schema_def folQ
    · exact fol_to_ra_query.evalT folQ hμ hdisj

theorem fol_to_ra (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema (FreshAtts (toPrenex folQ)) (FOL.BoundedQuery.toFormula folQ)) :
  ∃raQ : RA.Query _ _, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluateAdom dbi := by
    use fol_to_ra_query folQ
    use fol_to_ra_query.isWellTyped_def folQ
    exact fol_to_ra_eval folQ hμ hdisj

end FOLtoRA
