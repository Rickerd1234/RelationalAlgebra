import RelationalAlgebra.FOL.ModelTheoryFOL
import Mathlib.ModelTheory.Basic

open FOL Language RM


inductive BoundedQuery (dbi : DatabaseInstance) : ℕ → Type
  | R {n}: RelationName → BoundedQuery dbi n
  | and {n} {q1 q2 : BoundedQuery dbi n}: BoundedQuery dbi n
  | ex {n} {q : BoundedQuery dbi (n + 1)} : BoundedQuery dbi n
  -- | bdEqual

abbrev Query (dbi : DatabaseInstance) := BoundedQuery dbi 0

def EvaluateSchema {dbi : DatabaseInstance} (q : Query dbi) : RelationSchema := sorry

def EvaluateTuples {dbi : DatabaseInstance} (q : Query dbi) : Set Tuple := sorry

theorem evaluate_dom {dbi : DatabaseInstance} (q : Query dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = EvaluateSchema q := sorry

def Evaluate {dbi : DatabaseInstance} (q : Query dbi) : RelationInstance := ⟨EvaluateSchema q, EvaluateTuples q, evaluate_dom q⟩
