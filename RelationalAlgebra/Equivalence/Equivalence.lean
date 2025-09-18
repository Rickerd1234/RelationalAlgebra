import RelationalAlgebra.Equivalence.RAtoFOL.Relation
import RelationalAlgebra.Equivalence.RAtoFOL.Selection
import RelationalAlgebra.Equivalence.RAtoFOL.Projection
import RelationalAlgebra.Equivalence.RAtoFOL.Join
import RelationalAlgebra.Equivalence.RAtoFOL.Rename

open RM

theorem ra_to_fol_evalT.mp {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn => exact R_def.mp
    | s a b p sq ih => exact s_def.mp h ih
    | p rs q ih => exact p_def.mp h ih
    | j q₁ q₂ ih₁ ih₂ => exact j_def.mp h ih₁ ih₂
    | r f q ih => exact r_def.mp h ih

theorem ra_to_fol_evalT.mpr {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, t ∈ RA.Query.evaluateT dbi raQ → (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    induction raQ with
    | R rn => exact R_def.mpr h
    | s a b p sq ih => exact s_def.mpr h ih
    | p rs sq ih => exact p_def.mpr h ih
    | j q₁ q₂ ih₁ ih₂ => exact j_def.mpr h ih₁ ih₂
    | r f q ih => exact r_def.mpr h ih

theorem ra_to_fol_evalT.mem (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema):
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t ↔ t ∈ raQ.evaluateT dbi := by
    intro t
    apply Iff.intro
    . exact ra_to_fol_evalT.mp h_ra_wt t
    . exact ra_to_fol_evalT.mpr h_ra_wt t

theorem ra_to_fol_eval {dbi} [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema) :
  (ra_to_fol_query raQ dbi.schema).evaluate dbi = raQ.evaluate dbi h_ra_wt := by
    simp [RA.Query.evaluate, FOL.Query.evaluate, FOL.Query.evaluateT.def]
    simp_all
    ext t
    -- simp_all only [ra_to_fol_evalT.FOL_evaluateT]
    exact ra_to_fol_evalT.mem dbi raQ h_ra_wt t

theorem ra_to_fol {dbi} [FOL.folStruc dbi] (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.Query, folQ.evaluate dbi = raQ.evaluate dbi h := by
    use ra_to_fol_query raQ dbi.schema
    exact ra_to_fol_eval raQ h


theorem fol_to_ra {dbi} [FOL.folStruc dbi] (folQ : FOL.Query) (h : folQ.isWellTyped dbi.schema) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
