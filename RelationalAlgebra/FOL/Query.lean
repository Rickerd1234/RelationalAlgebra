import RelationalAlgebra.FOL.Relation

open FOL FirstOrder Language RM Term

namespace FOL

-- Query syntax
inductive BoundedQuery : ℕ → Type
  | R {n}: (brtr : BoundedRelationTermRestriction n) → BoundedQuery n
  | and {n} (q1 q2 : BoundedQuery n): BoundedQuery n
  | ex {n} (q : BoundedQuery (n + 1)) : BoundedQuery n
  -- | all {n} (q : BoundedQuery (n + 1)) : BoundedQuery n
  -- | not {n} (q : BoundedQuery n) : BoundedQuery n

abbrev Query := BoundedQuery 0

def BoundedQuery.toFormula {n : ℕ} : (q : BoundedQuery n) → fol.BoundedFormula Variable n
  | .R brtr => Relations.boundedFormula (.R brtr.dbi brtr.name) (getMap brtr)
  | .and q1 q2 => q1.toFormula ⊓ q2.toFormula
  | .ex q => .ex q.toFormula
  -- | .all q => .all q.toFormula
  -- | .not q => .not q.toFormula

def BoundedQuery.Realize {n : ℕ} [folStruc] : BoundedQuery n → (Variable →. Value) → (Fin n →. Value) → Prop
  | q, ov, iv => q.toFormula.Realize ov iv

def BoundedQuery.RealizeDom {n : ℕ} (dbi : DatabaseInstance) [folStruc] : BoundedQuery n → (Variable →. Value) → (Fin n →. Value) → Prop
  | ex q, ov, iv  => (∃a ∈ dbi.domain, q.toFormula.Realize ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain
  -- | all q, ov, iv => (∀a ∈ dbi.domain, q.toFormula.Realize ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain
  | q, ov, iv     => q.toFormula.Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Variable → Part Value) : Prop :=
  φ.RealizeDom dbi v (λ _ => .none)

@[simp]
theorem query_realize_def {n} [folStruc] {q : BoundedQuery n} {ov : Variable →. Value} {iv : Fin n →. Value}
  :  (q.Realize ov iv ↔ q.toFormula.Realize ov iv) := by
    simp_all [BoundedQuery.Realize, BoundedQuery.toFormula]

@[simp]
theorem query_realize_rel [folStruc] {n : ℕ} {dbi : DatabaseInstance} {brtr : BoundedRelationTermRestriction n} {ov : Variable →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.R brtr).RealizeDom dbi ov iv ↔ (Relations.boundedFormula (relations.R brtr.dbi brtr.name) (getMap brtr)).Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    simp_all only [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]

@[simp]
theorem query_realize_and [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q1 : BoundedQuery n} {q2 : BoundedQuery n} {ov : Variable →. Value} {iv : Fin n →. Value}
  : (q1.and q2).RealizeDom dbi ov iv ↔ (q1.Realize ov iv ∧ q2.Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain) := by
    simp_all only [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]
    aesop

-- @[simp]
-- theorem query_realize_not [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q : BoundedQuery n} {ov : Variable →. Value} {iv : Fin n →. Value}
--   : (q.not).RealizeDom dbi ov iv ↔ ¬(q.Realize ov iv) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
--     simp_all [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]

-- @[simp]
-- theorem query_realize_all [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q : BoundedQuery (n + 1)} {ov : Variable →. Value} {iv : Fin n →. Value}
--   : (q.all).RealizeDom dbi ov iv ↔ (∀ a ∈ dbi.domain, q.RealizeDom dbi ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
--     simp_all [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]

@[simp]
theorem query_realize_ex [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q : BoundedQuery (n + 1)} {ov : Variable →. Value} {iv : Fin n →. Value}
  : (q.ex).RealizeDom dbi ov iv ↔ (∃ a ∈ dbi.domain, q.Realize ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    simp_all [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]

-- Evaluation auxiliaries
def BoundedQuery.variablesInQuery {n : ℕ} : BoundedQuery n → Finset Variable
  | .R brtr    => brtr.outVars
  | .and q1 q2 => q1.variablesInQuery ∪ q2.variablesInQuery
  | .ex q      => q.variablesInQuery
  -- | .all q     => q.variablesInQuery
  -- | .not q     => q.variablesInQuery

def BoundedQuery.brtrInQuery {n m : ℕ} : BoundedQuery n → BoundedRelationTermRestriction m → Prop
  | .R brtr,    needle => dite (m ≥ n) (λ h => brtr.lift h = needle) (λ _ => False)
  | .and q1 q2, needle => q1.brtrInQuery needle ∨ q2.brtrInQuery needle
  | .ex q,      needle => q.brtrInQuery needle
  -- | .all q,     needle => q.brtrInQuery needle
  -- | .not q,     needle => q.brtrInQuery needle



structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  outFn : Attribute →. Variable -- @TODO: Check if this reversing makes it possible to mimic x = y through subst → x,x
  fintypeDom : Fintype outFn.Dom -- Required, since otherwise there is no restriction on outFn in this direction
  varsInQuery : outFn.ran.toFinset = query.variablesInQuery

instance {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : Fintype q.outFn.Dom := q.fintypeDom

@[simp]
theorem vars_in_query_def {var : Variable} {dbi : DatabaseInstance} {q : EvaluableQuery dbi}
  :  var ∈ q.query.variablesInQuery ↔ (∃ att, var ∈ q.outFn att) := by
    simp_all only [← q.varsInQuery, PFun.ran, Set.mem_toFinset, Set.mem_setOf_eq]
