import RelationalAlgebra.FOL.ModelTheoryFOL

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

def BoundedQuery.Realize {n : ℕ} (dbi : DatabaseInstance) [folStruc] (q : BoundedQuery n) :
  (Variable → Part Value) → (Fin n → Part Value) → Prop :=
    q.toFormula.Realize

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
  | .R rtr     => variablesInRTR rtr
  | .and q1 q2 => variablesInQuery q1 ∪ variablesInQuery q2
  | .ex q      => variablesInQuery q

structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  outFn : Attribute →. Variable -- @TODO: Check if reversing this makes it possible to have x = y subst → x,x
  varsInQuery : outFn.ran = variablesInQuery query
  fintypeDom : Fintype outFn.Dom -- Required, since otherwise there is no restriction on outFn in this direction

instance {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : Fintype q.outFn.Dom := q.fintypeDom

def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : RelationSchema :=
  q.outFn.Dom.toFinset

-- Evaluation logic
def EvaluateTuples {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : Set Tuple :=
{t |
  ∀a v bv, q.outFn a = some v → (bv v = t a ↔ (q.query.Realize dbi bv ∧ a ∈ q.schema))
}

theorem evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t h
  ext a
  simp_all only [PFun.mem_dom, Finset.mem_coe]
  sorry

def Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, EvaluateTuples q, evaluate_dom q⟩
