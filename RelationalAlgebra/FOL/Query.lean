import RelationalAlgebra.FOL.ModelTheoryFOL

open FOL FirstOrder Language RM

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n}: (rtr : RelationTermRestriction n) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedRelation {n : ℕ} {dbi : DatabaseInstance} (rtr : BoundedRelationTermRestriction n dbi) : fol.BoundedFormula Variable n :=
  Relations.boundedFormula (.R rtr.name rtr.schema) (getMap rtr)

def BoundedQuery.toFormula {n : ℕ} (dbi : DatabaseInstance) (q : BoundedQuery n) : fol.BoundedFormula Variable n :=
  match q with
  | .R rtr => BoundedRelation (rtr.toBounded dbi (h))
  | .and q1 q2 => (q1.toFormula dbi) ⊓ (q2.toFormula dbi)
  | .ex q => .ex (q.toFormula dbi)

def BoundedQuery.Realize [folStruc] {n : ℕ} (q : BoundedQuery n) (dbi : DatabaseInstance) :
  (Variable → Part Value) → (Fin n → Part Value) → Prop :=
    (q.toFormula dbi).Realize

nonrec def Query.Realize [folStruc] (φ : Query) (dbi : DatabaseInstance) (v : Variable → Part Value) : Prop :=
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

def variablesInRTR {n : ℕ} {dbi : DatabaseInstance} (rtr : BoundedRelationTermRestriction n dbi) : Finset Variable :=
  rtr.vars.filterMap VariableTerm.outVar? VariableTerm.outVar?.injective

def variablesInQuery {n : ℕ} : BoundedQuery n → DatabaseInstance → Finset Variable
  | .R rtr    , dbi=> variablesInRTR (rtr.toBounded dbi (h))
  | .and q1 q2, dbi=> variablesInQuery q1 dbi ∪ variablesInQuery q2 dbi
  | .ex q     , dbi=> variablesInQuery q dbi

structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  schema : RelationSchema
  outFn : Attribute →. Variable -- @TODO: Check if reversing this makes it possible to have x = y subst → x,x
  varsInQuery : outFn.ran = variablesInQuery query dbi
  domIsSchema : outFn.Dom = schema -- Required, since otherwise there is no restriction on outFn in this direction

-- Evaluation logic
def EvaluateTuples {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : Set Tuple :=
{t |
  ∀a v bv, q.outFn a = some v → (bv v = t a ↔ (q.query.Realize dbi bv ∧ a ∈ q.schema))
}

theorem evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t h
  ext a
  simp_all only [PFun.mem_dom, Finset.mem_coe, ← q.domIsSchema]
  apply Iff.intro
  · intro ⟨w, h_1⟩
    sorry
  · intro ⟨w, h_1⟩
    sorry

def Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, EvaluateTuples q, evaluate_dom q⟩
