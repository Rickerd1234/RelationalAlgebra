import RelationalAlgebra.FOL.ModelTheoryFOL

open FOL FirstOrder Language RM

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
  | ex q, ov, iv  => (∃a ∈ dbi.domain, q.RealizeDom dbi ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain
  -- | all q, ov, iv => ∀a ∈ dbi.domain, q.RealizeDom dbi ov (Fin.snoc iv a)
  | q, ov, iv     => q.toFormula.Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Variable → Part Value) : Prop :=
  φ.RealizeDom dbi v (λ _ => .none)

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
  | .R brtr    => variablesInRTR brtr.toRelationTermRestriction
  | .and q1 q2 => variablesInQuery q1 ∪ variablesInQuery q2
  | .ex q      => variablesInQuery q
  -- | .all q     => variablesInQuery q
  -- | .not q     => variablesInQuery q

structure EvaluableQuery (dbi : DatabaseInstance) where
  query : Query
  outFn : Attribute →. Variable -- @TODO: Check if this reversing makes it possible to mimic x = y through subst → x,x
  fintypeDom : Fintype outFn.Dom -- Required, since otherwise there is no restriction on outFn in this direction
  varsInQuery : outFn.ran.toFinset = variablesInQuery query

instance {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : Fintype q.outFn.Dom := q.fintypeDom

def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : RelationSchema :=
  q.outFn.Dom.toFinset

-- Evaluation logic
def VariableAssignmentToTuple {dbi : DatabaseInstance} (q : EvaluableQuery dbi) (ov : Variable →. Value) : Tuple
  := (λ att => ((q.outFn att).bind ov))

def EvaluableQuery.EvaluateTuples {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : Set Tuple :=
{t |
  ∃ov, q.query.Realize dbi ov ∧ t = VariableAssignmentToTuple q ov
}

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
  : (q.ex).RealizeDom dbi ov iv ↔ (∃ a ∈ dbi.domain, q.RealizeDom dbi ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    simp_all [BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]

@[simp]
theorem query_realizeDom_def {dbi} [folStruc] {q : Query} {ov : Variable →. Value}
  : q.Realize dbi ov ↔ q.toFormula.Realize ov (λ x => .none) ∧ ov.ran ⊆ dbi.domain := by
    simp_all [Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]
    have z : (PFun.ran fun (x : Fin 0) ↦ Part.none) ⊆ dbi.domain := by simp [PFun.ran]
    cases q with
    | and q1 q2 =>
      simp_all only [query_realize_and, query_realize_def, and_true, BoundedQuery.toFormula,
        BoundedFormula.realize_inf]
      exact Iff.symm and_assoc
    | ex qs =>
        sorry
    | _ => aesop

@[simp]
theorem query_realizeDom_vars {att} {dbi} [folStruc] {q : EvaluableQuery dbi} {ov : Variable →. Value}
  : (∃t, t ∈ q.EvaluateTuples) → ∀var ∈ variablesInQuery q.query, var ∈ q.outFn att → (ov var).Dom := by
    intro a
    simp_all only [query_realizeDom_def, EvaluableQuery.schema, q.varsInQuery, PFun.ran, DatabaseInstance.domain, variablesInQuery, ne_eq,
      EvaluableQuery.EvaluateTuples
    ]
    simp_all only [Set.mem_image, Set.setOf_subset_setOf, forall_exists_index]
    obtain ⟨left, right⟩ := a
    intro a var h_var
    simp_all only [Set.mem_setOf_eq]
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    obtain ⟨left_1, right_1⟩ := left_1
    rw [← q.varsInQuery] at var
    simp_all [PFun.ran]
    obtain ⟨w_1, h⟩ := var

    -- sorry
    have hz : w_1 ∈ left.Dom := by
      simp_all [VariableAssignmentToTuple]; apply exists_comm.mp; use a;
      subst right
      simp_all only [true_and]
      sorry
    have ⟨z, z_def⟩ : ∃v, v = (left w_1).get hz := by simp_all only [exists_eq]
    apply Part.dom_iff_mem.mpr
    use z
    subst right z_def
    simp_all [VariableAssignmentToTuple, Part.bind, Part.assert, Part.get]


@[simp]
theorem realize_query_dom {ov : Variable →. Value} {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) :
  q.query.Realize dbi ov → (VariableAssignmentToTuple q ov).Dom = q.schema := by
    intro h
    unfold VariableAssignmentToTuple EvaluableQuery.schema
    simp_all only [PFun.dom_mk, Part.bind_dom, Set.coe_toFinset]
    ext att
    simp_all only [Set.mem_setOf_eq, PFun.mem_dom]
    apply Iff.intro
    · intro ⟨w, h_1⟩
      exact Part.dom_iff_mem.mp w
    · intro ⟨w, w_1, h_1⟩
      subst h_1
      simp_all only [exists_true_left]
      simp_all [Part.dom_iff_mem]
      have ⟨val, w_2, h_var, h_val⟩ : ∃ val var, q.outFn att = Part.some var ∧ ov var = Part.some val := by--(q_att_dom_exists_val_var w_1 h)
        simp_all [Part.dom_iff_mem]
        obtain ⟨var, h_1⟩ := w_1
        apply exists_comm.mp
        simp_all only [exists_and_left]
        use var
        apply And.intro
        · exact Part.eq_some_iff.mpr h_1
        . simp_all [Part.eq_some_iff, ← Part.dom_iff_mem]
          have h1 : ∃t, t ∈ q.EvaluateTuples := by simp_all [EvaluableQuery.EvaluateTuples]; aesop
          apply query_realizeDom_vars h1
          . simp_all [← q.varsInQuery]
            obtain ⟨left, right⟩ := h
            obtain ⟨w, h⟩ := h1
            apply (PFun.mem_image q.outFn var q.outFn.Dom).mpr
            aesop
          . exact h_1
      simp_all only [Part.get_some, Part.mem_some_iff, exists_eq]

theorem EvaluableQuery.evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t ov h
  by_cases h2 : q.query.Realize dbi ov
  . intro a a_1
    subst a_1
    simp_all only [query_realizeDom_def, and_self, realize_query_dom]
  . intro a a_1
    subst a_1
    simp_all only [query_realizeDom_def, and_self, not_true_eq_false]

def EvaluableQuery.Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, q.EvaluateTuples, q.evaluate_dom⟩
