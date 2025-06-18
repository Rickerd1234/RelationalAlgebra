import RelationalAlgebra.FOL.ModelTheoryFOL
import Mathlib.ModelTheory.Basic

open FOL FirstOrder Language RM

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n}: (rtr : RelationTermRestriction n) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n
  | equal {n} (v1 v2 : VariableTerm n) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedQuery.toFormula {n : ℕ} (q : BoundedQuery n) : fol.BoundedFormula Variable n :=
  match q with
  | .R rtr => Relations.boundedFormula (.R rtr.name rtr.schema) (getMap rtr)
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  | .equal v1 v2 => .equal v1 v2

def BoundedQuery.Realize {n : ℕ} (dbi : DatabaseInstance) [folStruc dbi] (q : BoundedQuery n) :
  (Variable → Part Value) → (Fin n → Part Value) → Prop :=
    q.toFormula.Realize

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc dbi] (v : Variable → Part Value) : Prop :=
  φ.Realize dbi v default

-- Evaluation auxiliaries
def varEquiv {n : ℕ} : Variable → VariableTerm n → Prop
  | v1, .var v2 => v1 = v2.getLeft?

def variableInRTR {n : ℕ} (rtr : RelationTermRestriction n) (v : Variable) : Prop :=
  ∃a, (h: a ∈ rtr.schema) → varEquiv v ((rtr.fn a).get (by simp_all [Part.dom_iff_mem, ← PFun.mem_dom, rtr.validSchema, RelationTermRestriction.schema, h]))

def variableInQuery {n : ℕ} : BoundedQuery n → Variable → Prop
  | .R rtr,         v => variableInRTR rtr v
  | .and q1 q2,     v => variableInQuery q1 v ∨ variableInQuery q2 v
  | .ex q,          v => variableInQuery q v
  | .equal v1 v2,   v => varEquiv v v1 ∨ varEquiv v v2

structure EvaluatableQuery (dbi : DatabaseInstance) where
  query : Query
  schema : RelationSchema
  outFn : Variable →. Attribute
  injective : outFn.Injective
  varInQuery : outFn.Dom = {v | variableInQuery query v}
  validSchema : schema.toSet = {a | ∀v, variableInQuery query v ∧ outFn v = some a}

-- Evaluation logic
def EvaluateSchema {dbi : DatabaseInstance} (q : EvaluatableQuery dbi) : RelationSchema := q.schema

def EvaluateTuples {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluatableQuery dbi) : Set Tuple :=
{t |
  ∀a v bv, q.outFn v = some a → (bv v = t a ↔ (q.query.Realize dbi bv ∧ a ∈ q.schema))
}

theorem evaluate_dom {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluatableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = EvaluateSchema q := by
  simp [EvaluateSchema, EvaluateTuples]
  intro t h
  ext a
  simp_all only [PFun.mem_dom, Finset.mem_coe]
  apply Iff.intro
  · intro ⟨val, val_ta⟩
    apply Finset.mem_coe.mp
    simp_all only [Set.mem_setOf_eq, Part.coe_some, q.validSchema]
    intro v
    apply And.intro
    · sorry
    · sorry
  · intro a_qs
    apply Finset.mem_coe.mpr at a_qs
    simp_all only [q.validSchema, Part.coe_some, Set.mem_setOf_eq, Part.some_inj]
    sorry

def Evaluate {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluatableQuery dbi)
  : RelationInstance := ⟨EvaluateSchema q, EvaluateTuples q, evaluate_dom q⟩
