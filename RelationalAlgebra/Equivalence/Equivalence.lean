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
- `α` carries a decidable linear order (`[LinearOrder α]`)
- value type `μ` to be inhabited (have a `default` value)
-/
section RAtoFOL

variable {ρ α μ : Type} {dbi : DatabaseInstance ρ α μ} [LinearOrder α] [FOL.folStruc dbi] [Inhabited μ]
  (raQ : RA.Query ρ α) (h : RA.Query.isWellTyped dbi.schema raQ)

/-- Query evaluation equivalence for a set of tuples -/
theorem toFOL.evalT_def (h : RA.Query.isWellTyped dbi.schema raQ) :
  (toFOL dbi.schema raQ).evaluateT dbi = raQ.evaluateT dbi := by
    induction raQ with
    | R rn => exact toFOL.evalT_def.R_def_eq h
    | s a b sq ih => exact toFOL.evalT_def.s_def_eq h (ih h.1)
    | p rs sq ih => exact toFOL.evalT_def.p_def_eq h (ih h.1)
    | j q₁ q₂ ih₁ ih₂ => exact toFOL.evalT_def.j_def_eq h (ih₁ h.1) (ih₂ h.2)
    | r f q ih => exact toFOL.evalT_def.r_def_eq h (ih h.1)
    | u q₁ q₂ ih₁ ih₂ => exact toFOL.evalT_def.u_def_eq h (ih₁ h.1) (ih₂ h.2.1)
    | d q nq ih nih => exact toFOL.evalT_def.d_def_eq h (ih h.1) (nih h.2.1)

/-- Query evaluation equivalence for `RelationInstance` -/
theorem toFOL_eval :
  (toFOL dbi.schema raQ).evaluateAdom dbi = raQ.evaluate dbi h := by
    simp [RA.Query.evaluate, FOL.Query.evaluateAdom, h,
      toFOL.schema_def, toFOL.evalT_def raQ h]
    exact RA.Query.evaluateT.dbi_domain h

/-- Query expressivity equivalence -/
theorem ra_to_fol_equivalence :
  ∃folQ : FOL.Query dbi.schema, folQ.evaluateAdom dbi = raQ.evaluate dbi h := by
    use toFOL dbi.schema raQ
    exact toFOL_eval raQ h

end RAtoFOL

/-!
### FOL → RA Equivalence

Requires:
**Type / order structure**
- Attribute type `α` and relation symbol type `ρ` are inhabited (required for computable definitions)
- `α` and `ρ` carry a decidable linear order (`[LinearOrder α]`, `[LinearOrder ρ]`)
  (used for computability of evaluation, folds and conversion between named and unnamed perspective)
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
theorem queryToRA_eval (brs_disj : folQ.schema ∩ brs = ∅) (brs_depth : 0 + FOL.depth (toPrenex folQ) < brs.card) (brs_def : default ∉ brs)
  (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema brs (folQ.toFormula)) (hdef : default ∉ folQ.schema) :
    (queryToRA folQ brs).evaluate dbi (queryToRA.isWellTyped_def folQ brs_disj brs_depth) = folQ.evaluateAdom dbi := by
      simp only [RA.Query.evaluate, FOL.Query.evaluateAdom, RelationInstance.mk.injEq]
      apply And.intro
      · exact queryToRA.schema_def folQ
      · exact queryToRA.evalT_def folQ hμ hdisj hdef brs_disj brs_depth brs_def

/-- Query expressivity equivalence -/
theorem fol_to_ra_equivalence (brs : Finset α) (brs_disj : folQ.schema ∩ brs = ∅) (brs_depth : 0 + FOL.depth (toPrenex folQ) < brs.card) (brs_def : default ∉ brs)
  (hμ : ∀v, v ∈ dbi.domain) (hdisj : FOL.disjointSchema brs (folQ.toFormula)) (hdef : default ∉ folQ.schema) :
    ∃raQ : RA.Query _ _, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluateAdom dbi := by
      use queryToRA folQ brs
      use queryToRA.isWellTyped_def folQ brs_disj brs_depth
      exact queryToRA_eval folQ brs brs_disj brs_depth brs_def hμ hdisj hdef

end FOLtoRA
