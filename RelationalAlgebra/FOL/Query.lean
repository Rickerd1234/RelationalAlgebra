import RelationalAlgebra.FOL.ModelTheoryFOL

open FOL FirstOrder Language RM Term

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
  -- | all q, ov, iv => (∀a ∈ dbi.domain, q.RealizeDom dbi ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain
  | q, ov, iv     => q.toFormula.Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain

nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Variable → Part Value) : Prop :=
  φ.RealizeDom dbi v (λ _ => .none)

-- Evaluation auxiliaries
def BoundedQuery.variablesInQuery {n : ℕ} : BoundedQuery n → Finset Variable
  | .R brtr    => brtr.outVars
  | .and q1 q2 => q1.variablesInQuery ∪ q2.variablesInQuery
  | .ex q      => q.variablesInQuery
  -- | .all q     => q.variablesInQuery
  -- | .not q     => q.variablesInQuery

def BoundedQuery.brtrInQuery {n m : ℕ} : BoundedQuery n → BoundedRelationTermRestriction m → Prop
  | .R brtr,    needle => dite (m ≤ n) (λ h => brtr = needle.lift h) (λ _ => False)
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

def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : RelationSchema :=
  q.outFn.Dom.toFinset

@[simp]
theorem vars_in_query_def {var : Variable} {dbi : DatabaseInstance} {q : EvaluableQuery dbi}
  :  var ∈ q.query.variablesInQuery ↔ (∃ att, var ∈ q.outFn att) := by
    simp_all only [← q.varsInQuery, PFun.ran, Set.mem_toFinset, Set.mem_setOf_eq]

@[simp]
theorem vars_in_query_brtr_def {n m: ℕ} {var : Variable} {query : BoundedQuery n}
  : m ≤ n → (var ∈ query.variablesInQuery ↔ ∃brtr : BoundedRelationTermRestriction m, var ∈ brtr.outVars ∧ query.brtrInQuery brtr) := by
    induction query with
    | R brtr =>
      rename ℕ => n'
      simp_all only [BoundedQuery.variablesInQuery, RelationTermRestriction.outVars,
        RelationTermRestriction.vars, Finset.mem_filterMap, Set.mem_toFinset, outVar?,
        BoundedQuery.brtrInQuery, BoundedRelationTermRestriction.lift, dite_true, liftInFn, Term.relabel, Sum.map, PFun.ran]
      intro a
      simp_all only [Set.mem_setOf_eq, dite_else_false]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := left
        split at right
        next x x_1 =>
          simp_all only [Sum.getLeft?_eq_some_iff]
          subst right
          sorry
        next x x_1 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := left
        obtain ⟨left, right_1⟩ := h
        obtain ⟨w_2, h⟩ := left
        subst right
        simp_all only
        split at right_1
        next x x_1 =>
          simp_all only [Sum.getLeft?_eq_some_iff]
          subst right_1
          sorry
        next x x_1 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
    | and q1 q2 h1 h2 =>
      intro a
      simp_all [BoundedQuery.variablesInQuery]
      apply Iff.intro
      · intro a_1
        cases a_1 with
        | inl h =>
          simp_all only [iff_true]
          obtain ⟨w, h⟩ := h
          obtain ⟨left, right⟩ := h
          simp_all [BoundedQuery.brtrInQuery]
          apply Exists.intro
          · apply And.intro
            · exact left
            · simp_all only [true_or]
        | inr h_1 =>
          simp_all only [iff_true]
          obtain ⟨w, h⟩ := h_1
          obtain ⟨left, right⟩ := h
          simp_all [BoundedQuery.brtrInQuery]
          apply Exists.intro
          · apply And.intro
            · exact left
            · simp_all only [or_true]
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        simp_all [BoundedQuery.brtrInQuery]
        aesop
    | _ q q_ih =>
      rename ℕ => n'
      intro a
      have z : m ≤ n' + 1 := by exact Nat.le_add_right_of_le a
      simp_all [BoundedQuery.brtrInQuery, BoundedQuery.variablesInQuery]

-- Evaluation logic
def VariableAssignmentToTuple {dbi : DatabaseInstance} (q : EvaluableQuery dbi) (ov : Variable →. Value) : Tuple
  := (λ att => ((q.outFn att).bind ov))

theorem realize_relation_dom [folStruc] {n ov iv var} (q : BoundedQuery n)
  (h1 : var ∈ q.variablesInQuery) (h2 : q.Realize ov iv)
  : (ov var).Dom := by
    induction q with
    | R brtr =>
      simp_all only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_rel]
      -- @TODO: Finish most promising proof yet, by creating separate function for this h_map
      -- have h_map : (Fin (Finset.card (brtr.dbi.schema brtr.name))) →. Value
      --   := (λ i => ((brtr.inFn (brtr.schema.fromIndex ⟨i, by simp [← brtr_schema_dbi_def]⟩)).get (by sorry)).realize (Sum.elim ov iv))
      have h3 := (folStruc.RelMap_R brtr.dbi brtr.name (fun i ↦ realize (Sum.elim ov iv) (getMap brtr i))).mpr h2
      have v : ∀att, (h : att ∈ brtr.schema) →
        ((fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)) ⟨brtr.schema.index h, by simp⟩).Dom := by
          sorry
      simp_all only

      simp [BoundedQuery.variablesInQuery, RelationTermRestriction.outVars, RelationTermRestriction.vars] at h1
      obtain ⟨w, h⟩ := h1
      obtain ⟨left, right⟩ := h
      rw [PFun.ran] at left
      simp_all only [Set.mem_setOf_eq]
      obtain ⟨w_1, h⟩ := left
      have z : w_1 ∈ brtr.schema := by simp [brtr_schema_dbi_def]; apply att_in_dom.mp; use w
      have z2 := v w_1 z
      simp_all [outVar?, getMap]
      sorry






    | and q1 q2 q1_ih q2_ih =>
      simp only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_inf] at h2
      simp only [BoundedQuery.variablesInQuery, Finset.mem_union] at h1
      obtain ⟨left, right⟩ := h2
      cases h1 with
      | inl h => exact q1_ih h left
      | inr h => exact q2_ih h right
    | ex qs qs_ih =>
      simp_all only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_ex]
      simp_all only [Nat.succ_eq_add_one]
      obtain ⟨w, h⟩ := h2
      apply @qs_ih
      · exact h1
      · exact h

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
  : q.toFormula.Realize ov (λ x => .none) ∧ ov.ran ⊆ dbi.domain → q.Realize dbi ov:= by
    simp_all [Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]
    have z : (PFun.ran fun (x : Fin 0) ↦ Part.none) ⊆ dbi.domain := by simp [PFun.ran]
    cases q with
    | and q1 q2 =>
      simp_all only [query_realize_and, query_realize_def, and_true, BoundedQuery.toFormula,
        BoundedFormula.realize_inf]
      exact fun a a ↦ trivial
    | ex qs =>
        intro a a_1
        simp_all only [query_realize_ex, Nat.reduceAdd, Part.coe_some, and_self, and_true]
        simp_all [Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula]
        -- @TODO: Make this recusion?! work, and see if it can be a ↔ theorem instead of →
        sorry
    | _ => aesop

def FOL.BoundedRelationTermRestriction.realize [folStruc] {n : ℕ} (brtr : BoundedRelationTermRestriction n) (t : Tuple) (v : (Variable ⊕ Fin n) →. Value) : Prop :=
  ∀att, t att = (brtr.inFn att).map (λ var => var.realize v)

theorem relmap_eq_brtr_realize [folStruc] {n : ℕ} (brtr : BoundedRelationTermRestriction n) (v : (Variable ⊕ Fin n) →. Value) :
  assignmentToTuple (λ i : Fin (Finset.card (brtr.dbi.schema brtr.name)) => ((brtr.inFn (brtr.schema.fromIndex ⟨i, by simp [← brtr_schema_dbi_def]⟩ )).bind (λ term => term.realize v))) ∈ (brtr.dbi.relations brtr.name).tuples ↔ ∃t, brtr.realize t v := by
    simp_all only [getMap, RelationSchema.fromIndex, RelationSchema.ordering, List.get_eq_getElem,
      brtr_schema_dbi_def, BoundedRelationTermRestriction.realize, Part.coe_some, Part.pure_eq_some,
      Part.bind_eq_bind]
    sorry

@[simp]
theorem query_realize_brtr_dom {n ov iv dbi} [folStruc] {q : EvaluableQuery dbi} {brtr : BoundedRelationTermRestriction n}
  : q.query.brtrInQuery brtr → ((BoundedQuery.R brtr).RealizeDom brtr.dbi ov iv ∧ ∃t, t ∈ brtr.relationInstance.tuples) → ∃t, brtr.realize t (Sum.elim ov iv) := by
    simp_all only [EvaluableQuery.EvaluateTuples, Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.toFormula, ne_eq, Set.mem_setOf_eq, vars_in_query_def,
      forall_exists_index, and_imp]
    intro brtr_in_query h_sat ov_dom iv_dom t h_t
    simp_all only [BoundedRelationTermRestriction.realize, BoundedFormula.realize_rel, Part.mem_bind_iff, exists_and_right, Part.coe_some, Part.pure_eq_some, Part.bind_eq_bind]
    use λ a => (brtr.inFn a).bind (λ var => var.realize (Sum.elim ov iv))
    intro att
    simp_all only
    simp_all [Part.bind_some_eq_map]
    ext pval
    simp_all only [Part.mem_bind_iff, Part.mem_map_iff]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      subst right
      use w
      simp_all only [true_and]
      exact Part.eq_some_iff.mpr left_1
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      use w
      simp_all only [true_and]
      have z : att ∈ t.Dom := by sorry -- @TODO: connect through left?
      use (t att).get z
      simp_all only [Part.some_get]
      have z2 : t att = realize (Sum.elim ov iv) w := by sorry
      simp_all only [and_true]
      exact Part.get_mem (z2 ▸ z)

theorem variable_assignment_ov_eq [folStruc] {iv ov1 ov2 dbi} {q : EvaluableQuery dbi} :
  BoundedQuery.RealizeDom dbi q.query ov1 iv → VariableAssignmentToTuple q ov1 = VariableAssignmentToTuple q ov2 → BoundedQuery.RealizeDom dbi q.query ov2 iv := by
    intro a a_1
    sorry



@[simp]
theorem query_realizeDom_vars {dbi} {var} [folStruc] {q : EvaluableQuery dbi} {ov}
  (h : VariableAssignmentToTuple q ov ∈ q.EvaluateTuples) (h2 : var ∈ q.query.variablesInQuery)
  : (ov var).Dom := by

    simp_all only [EvaluableQuery.EvaluateTuples, Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, ne_eq, Set.mem_setOf_eq, vars_in_query_def,
      forall_exists_index, and_imp]
    obtain ⟨h_ov, h⟩ := h
    obtain ⟨w_1, h_1⟩ := h2
    obtain ⟨left, right⟩ := h

    have h1 : var ∈ BoundedQuery.variablesInQuery q.query := by apply vars_in_query_def.mpr; use w_1
    have h2 : BoundedQuery.Realize q.query ov (λ x => .none) := by sorry

    apply realize_relation_dom q.query h1 h2



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
      have ⟨val, w_2, h_var, h_val⟩ : ∃ val var, q.outFn att = Part.some var ∧ ov var = Part.some val := by
        simp_all [Part.dom_iff_mem]
        obtain ⟨var, h_1⟩ := w_1
        apply exists_comm.mp
        simp_all only [exists_and_left]
        use var
        apply And.intro
        · exact Part.eq_some_iff.mpr h_1
        . simp_all [Part.eq_some_iff, ← Part.dom_iff_mem]
          have h_ov : VariableAssignmentToTuple q ov ∈ q.EvaluateTuples := by simp_all [EvaluableQuery.EvaluateTuples]; aesop
          apply query_realizeDom_vars ov h_ov
          . simp_all [← q.varsInQuery]
            apply (ran_mem q.outFn).mpr
            use att
            exact Part.eq_some_iff.mpr h_1
      simp_all only [Part.get_some, Part.mem_some_iff, exists_eq]

theorem EvaluableQuery.evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t ov h
  by_cases h2 : q.query.Realize dbi ov
  . intros; simp_all only [realize_query_dom]
  . simp_all only

def EvaluableQuery.Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, q.EvaluateTuples, q.evaluate_dom⟩
