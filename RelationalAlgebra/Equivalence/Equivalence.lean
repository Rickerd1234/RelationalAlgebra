import RelationalAlgebra.Equivalence.RAtoFOL.Relation
import RelationalAlgebra.Equivalence.RAtoFOL.Selection
import RelationalAlgebra.Equivalence.RAtoFOL.Projection
import RelationalAlgebra.Equivalence.RAtoFOL.Join
import RelationalAlgebra.Equivalence.RAtoFOL.Rename
import RelationalAlgebra.Equivalence.RAtoFOL.Union
import RelationalAlgebra.Equivalence.RAtoFOL.Diff
import RelationalAlgebra.Equivalence.FOLtoRA.Conversion

open RM

theorem ra_to_fol_evalT {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  (ra_to_fol_query raQ dbi.schema).evaluateT dbi = RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn => exact ra_to_fol_evalT.R_def_eq h
    | s a b sq ih => exact ra_to_fol_evalT.s_def_eq h (ih h.1)
    | p rs sq ih => exact ra_to_fol_evalT.p_def_eq h (ih h.1)
    | j q₁ q₂ ih₁ ih₂ => exact ra_to_fol_evalT.j_def_eq h (ih₁ h.1) (ih₂ h.2)
    | r f q ih => exact ra_to_fol_evalT.r_def_eq h (ih h.1)
    | u q₁ q₂ ih₁ ih₂ => exact ra_to_fol_evalT.u_def_eq h (ih₁ h.1) (ih₂ h.2.1)
    | d q nq ih nih => exact ra_to_fol_evalT.d_def_eq h (ih h.1) (nih h.2.1)

theorem ra_to_fol_eval {dbi} [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema) :
  (ra_to_fol_query raQ dbi.schema).evaluate dbi = raQ.evaluate dbi h_ra_wt := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    simp_all [ra_to_fol_query_schema]
    exact ra_to_fol_evalT h_ra_wt

theorem ra_to_fol {dbi} [FOL.folStruc dbi] (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.Query dbi.schema, folQ.evaluate dbi = raQ.evaluate dbi h := by
    use ra_to_fol_query raQ dbi.schema
    exact ra_to_fol_eval raQ h


theorem fol_to_ra_eval {dbi} [FOL.folStruc dbi] [Fintype (adomRs dbi.schema)] (q : FOL.Query dbi.schema):
  (toRA dbi.schema (toPrenex q)).evaluate dbi (toRA.isWellTyped_def q) = q.evaluate dbi := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    apply And.intro
    · exact toRA.schema_def dbi.schema
    · cases q with
      | _ => simp [FOL.Query.evaluateT, FOL.Query.RealizeMin.ex_def, FOL.BoundedQuery.Realize]; sorry

theorem fol_to_ra {dbi} [FOL.folStruc dbi] (folQ : FOL.Query dbi.schema) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
