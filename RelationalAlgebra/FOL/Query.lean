import RelationalAlgebra.FOL.ModelTheoryFOL
import Mathlib.ModelTheory.Basic

open FOL Language RM

-- Query syntax
inductive BoundedQuery (dbi : DatabaseInstance) : ℕ → Type
  | R {n}: (rn : RelationName) → (rtr : RelationTermRestriction n) → rtr.schema = dbi.schema rn → BoundedQuery dbi n
  | and {n} (q1 q2 : BoundedQuery dbi n): BoundedQuery dbi n
  | ex {n} (q : BoundedQuery dbi (n + 1)) : BoundedQuery dbi n
  | bdEqual {n} (v1 v2 : VariableTerm n) : BoundedQuery dbi n

abbrev Query (dbi : DatabaseInstance) := BoundedQuery dbi 0

-- Evaluation auxiliaries
def isBoundVar {n : ℕ} : VariableTerm n → Prop
  | .var v => v.isLeft

def varEquiv {n m : ℕ} : VariableTerm n → VariableTerm m → Prop
  | .var v1, .var v2 => v1.getLeft? = v2.getLeft?

def variableInRTR {n m : ℕ} (rtr : RelationTermRestriction n) (v1 : VariableTerm m) : Prop :=
  ∃a, (h: a ∈ rtr.schema) → varEquiv v1 ((rtr.fn a).get (by simp [Part.dom_iff_mem, ← PFun.mem_dom, rtr.validSchema, h]))

def variableInQuery {n : ℕ} {dbi : DatabaseInstance} : BoundedQuery dbi n → VariableTerm 0 → Prop
  | .R _ rtr _,     v => variableInRTR rtr v
  | .and q1 q2,     v => variableInQuery q1 v ∨ variableInQuery q2 v
  | .ex q,          v => variableInQuery q v
  | .bdEqual v1 v2, v => varEquiv v1 v ∨ varEquiv v2 v

structure EvaluatableQuery (dbi : DatabaseInstance) where
  query : Query dbi
  schema : RelationSchema
  outFn : VariableTerm 0 →. Attribute
  injective : outFn.Injective
  validSchema : ∀v, (h : v ∈ outFn.Dom) → isBoundVar v ∧ variableInQuery query v ∧ (outFn v).get (h) ∈ schema

-- Evaluation logic
def EvaluateSchema {dbi : DatabaseInstance} (q : EvaluatableQuery dbi) : RelationSchema := q.schema

def EvaluateTuples {dbi : DatabaseInstance} (q : EvaluatableQuery dbi) : Set Tuple := {t | ∀v : q.query}

theorem evaluate_dom {dbi : DatabaseInstance} (q : EvaluatableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = EvaluateSchema q := sorry

def Evaluate {dbi : DatabaseInstance} (q : EvaluatableQuery dbi)
  : RelationInstance := ⟨EvaluateSchema q, EvaluateTuples q, evaluate_dom q⟩
