import RelationalAlgebra.Equivalence.RAtoFOL.Relation
import RelationalAlgebra.Equivalence.RAtoFOL.Selection
import RelationalAlgebra.Equivalence.RAtoFOL.Projection
import RelationalAlgebra.Equivalence.RAtoFOL.Join
import RelationalAlgebra.Equivalence.RAtoFOL.Rename
import RelationalAlgebra.Equivalence.RAtoFOL.Union
import RelationalAlgebra.Equivalence.RAtoFOL.Diff
import RelationalAlgebra.Equivalence.FOLtoRA.Prenex
import RelationalAlgebra.FOL.EvaluateAdom

open RM

/-!
### RA → FOL Equivalence

Requires:
- the RA query to be well-typed
- value type `μ` to be inhabited (have a `default` value)
-/
section RAtoFOL

variable {ρ α μ : Type} {dbi : DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Inhabited μ]
  (raQ : RA.Query ρ α) (h : RA.Query.isWellTyped dbi.schema raQ)

/-- Query evaluation equivalence for a set of tuples -/
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

/-- Query evaluation equivalence for `RelationInstance` -/
theorem ra_to_fol_eval :
  (ra_to_fol_query dbi.schema raQ).evaluateAdom dbi = raQ.evaluate dbi h := by
    simp [RA.Query.evaluate, FOL.Query.evaluateAdom, h,
      ra_to_fol_query_schema, ra_to_fol_evalT raQ h]
    exact RA.Query.evaluateT.dbi_domain h

/-- Query expressivity equivalence -/
theorem ra_to_fol :
  ∃folQ : FOL.Query dbi.schema, folQ.evaluateAdom dbi = raQ.evaluate dbi h := by
    use ra_to_fol_query dbi.schema raQ
    exact ra_to_fol_eval raQ h

end RAtoFOL

/-!
### FOL → RA Equivalence

Requires:
**Type / order structure**
- Attribute type `α` and relation symbol type `ρ` are inhabited (required for computable definitions)
- `α` and `ρ` carry a decidable linear order (`[LinearOrder α]`, `[LinearOrder ρ]`)
  (used for computability of folds and conversion between named and unnamed perspective)
- Value domain type `μ` is inhabited (required for computable `TupleToFun` conversion)

**Database instance assumptions**
- A database instance `dbi : DatabaseInstance ρ α μ`
- The relations with nonempty relation schemas `adomRs dbi.schema` is finite and nonempty
  (required for computability of adom)
- All values of type `μ` lie in the database domain (`∀ v, v ∈ dbi.domain`)

**Query and bookkeeping assumptions**
- A first-order logic query `folQ : FOL.Query dbi.schema`
- A finite set of fresh attributes `brs : Finset α`
- `brs` is disjoint from the query schema
- `brs` is large enough to supply sufficient fresh variables (after prenex normalization)
- The value `default : α` is not contained in `brs`
- `default` does not appear in the free variables of the query
- `brs` is disjoint from all relation schemas and all relation schemas are disjoint from the free variables used for that relation
-/
section FOLtoRA

variable {ρ α μ : Type} [Inhabited α] [Inhabited ρ] [LinearOrder α] [LinearOrder ρ] [Inhabited μ]
  {dbi : DatabaseInstance ρ α μ} [FOL.folStruc dbi] [Fintype (adomRs dbi.schema)] [Nonempty (adomRs dbi.schema)]
  (folQ : FOL.Query dbi.schema)
  (brs : Finset α)

/-- Query evaluation equivalence for `RelationInstance` -/
theorem fol_to_ra_eval (brs_disj : folQ.schema ∩ brs = ∅) (brs_depth : 0 + FOL.depth (toPrenex folQ) < brs.card) (brs_def : default ∉ brs)
  (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema brs (folQ.toFormula)) (hdef : default ∉ folQ.schema) :
    (fol_to_ra_query folQ brs).evaluate dbi (fol_to_ra_query.isWellTyped_def folQ brs_disj brs_depth) = folQ.evaluateAdom dbi := by
      simp only [RA.Query.evaluate, FOL.Query.evaluateAdom, RelationInstance.mk.injEq]
      apply And.intro
      · exact fol_to_ra_query.schema_def folQ
      · exact fol_to_ra_query.evalT_def folQ hμ hdisj hdef brs_disj brs_depth brs_def

/-- Query expressivity equivalence -/
theorem fol_to_ra (brs : Finset α) (brs_disj : folQ.schema ∩ brs = ∅) (brs_depth : 0 + FOL.depth (toPrenex folQ) < brs.card) (brs_def : default ∉ brs)
  (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema brs (folQ.toFormula)) (hdef : default ∉ folQ.schema) :
    ∃raQ : RA.Query _ _, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluateAdom dbi := by
      use fol_to_ra_query folQ brs
      use fol_to_ra_query.isWellTyped_def folQ brs_disj brs_depth
      exact fol_to_ra_eval folQ brs brs_disj brs_depth brs_def hμ hdisj hdef

end FOLtoRA
