import RelationalAlgebra.FOL.ModelTheoryFOL

open FOL FirstOrder Language RM

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n}: (brtr : BoundedRelationTermRestriction n) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedQuery.toFormula {n : ℕ} (q : BoundedQuery n) : fol.BoundedFormula Variable n :=
  match q with
  | .R brtr => Relations.boundedFormula (.R brtr.dbi brtr.name) (getMap brtr)
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula

def BoundedQuery.Realize {n : ℕ} (dbi : DatabaseInstance) [folStruc] (q : BoundedQuery n)
  (fv : Variable →. Value) (bv : Fin n →. Value) : Prop :=
    q.toFormula.Realize fv bv ∧ fv.ran ⊆ dbi.domain ∧ bv.ran ⊆ dbi.domain

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Variable → Part Value) : Prop :=
  φ.Realize dbi v default

-- Evaluation auxiliaries
def VariableTerm.outVar? {n : ℕ} : (vt : VariableTerm n) → Option Variable
  | .var x => x.getLeft?
  | _ => none

theorem VariableTerm.outVar?.injective {n : ℕ} (a a' : VariableTerm n) : ∀ b ∈ VariableTerm.outVar? a, b ∈ VariableTerm.outVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, VariableTerm.outVar?]
    aesop

def variablesInRTR {n : ℕ} (rtr : RelationTermRestriction n) : Finset Variable :=
  rtr.vars.filterMap VariableTerm.outVar? VariableTerm.outVar?.injective

def variablesInQuery {n : ℕ} : BoundedQuery n → Finset Variable
  | .R brtr     => variablesInRTR brtr.toRelationTermRestriction
  | .and q1 q2 => variablesInQuery q1 ∪ variablesInQuery q2
  | .ex q      => variablesInQuery q

structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  outFn : Attribute →. Variable -- @TODO: Check if this reversing makes it possible to mimic x = y through subst → x,x
  fintypeDom : Fintype outFn.Dom -- Required, since otherwise there is no restriction on outFn in this direction
  varsInQuery : outFn.ran.toFinset = variablesInQuery query

instance {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : Fintype q.outFn.Dom := q.fintypeDom

def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : RelationSchema :=
  q.outFn.Dom.toFinset

-- Evaluation logic
def VariableAssignmentToTuple {dbi : DatabaseInstance} (q : EvaluableQuery dbi) (bv : Variable →. Value) : Tuple
  := (λ att => ((q.outFn att).bind bv))

def EvaluateTuples {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : Set Tuple :=
{t |
  ∀bv, q.query.Realize dbi bv ↔ t = VariableAssignmentToTuple q bv
}

theorem evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t h
  ext a
  simp_all only [PFun.mem_dom, Finset.mem_coe]
  sorry

def Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, EvaluateTuples q, evaluate_dom q⟩
