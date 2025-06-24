import RelationalAlgebra.FOL.ModelTheoryFOL
import Mathlib.ModelTheory.Basic

open FOL FirstOrder Language RM

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n}: (rtr : RelationTermRestriction n) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedQuery.toFormula {n : ℕ} (q : BoundedQuery n) : fol.BoundedFormula Variable n :=
  match q with
  | .R rtr => Relations.boundedFormula (.R rtr.name rtr.schema) (getMap rtr)
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula

def BoundedQuery.Realize {n : ℕ} (dbi : DatabaseInstance) [folStruc dbi] (q : BoundedQuery n) :
  (Variable → Part Value) → (Fin n → Part Value) → Prop :=
    q.toFormula.Realize

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc dbi] (v : Variable → Part Value) : Prop :=
  φ.Realize dbi v default

-- Evaluation auxiliaries
def VariableTerm.IsVariable (n : ℕ) : VariableTerm n → Prop
  | .var x => x.isLeft
  | _ => False

def VariableTerm.var (n : ℕ) : (vt : VariableTerm n) → VariableTerm.IsVariable n vt → Variable
  | .var x, h => x.getLeft h
  | _, _ => ""

def variablesInRTR {n : ℕ} [DecidablePred (VariableTerm.IsVariable n)] (rtr : RelationTermRestriction n) [Fintype rtr.fn.ran] : Finset Variable :=
  (rtr.fn.ran.toFinset.filter (VariableTerm.IsVariable n)).image VariableTerm.var n -- @TODO: Make this work

def variablesInQuery {n : ℕ} : BoundedQuery n → Finset Variable
  | .R rtr     => variablesInRTR rtr
  | .and q1 q2 => variablesInQuery q1 ∪ variablesInQuery q2
  | .ex q      => variablesInQuery q

structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  outFn : Attribute →. Variable -- @TODO: Check if reversing this makes it possible to have x = y subst → x,x
  varsInQuery : outFn.ran = variablesInQuery query

-- Evaluation logic
def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) [Fintype q.outFn.Dom] : RelationSchema :=
  q.outFn.Dom.toFinset

def EvaluateTuples {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluableQuery dbi) [Fintype q.outFn.Dom] : Set Tuple :=
{t |
  ∀a v bv, q.outFn a = some v → (bv v = t a ↔ (q.query.Realize dbi bv ∧ a ∈ q.schema))
}

theorem evaluate_dom {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = EvaluateSchema q := by
  simp [EvaluateTuples]
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

def Evaluate {dbi : DatabaseInstance} [folStruc dbi] (q : EvaluableQuery dbi) [Fintype q.outFn.Dom]
  : RelationInstance := ⟨q.schema, EvaluateTuples q, evaluate_dom q⟩
