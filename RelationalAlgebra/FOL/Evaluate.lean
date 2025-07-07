import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

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
        ((fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)) ⟨brtr.schema.index h, by simp [← brtr_schema_dbi_def]⟩).Dom := by
          intro att h
          simp_all only
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
      simp_all only [brtr_schema_dbi_def]
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
theorem query_realizeDom_vars [folStruc] {dbi ov var} {q : EvaluableQuery dbi}
  (h : VariableAssignmentToTuple q ov ∈ q.EvaluateTuples) (h2 : var ∈ q.query.variablesInQuery)
  : (ov var).Dom := by

    simp_all only [EvaluableQuery.EvaluateTuples, Query.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, ne_eq, Set.mem_setOf_eq, vars_in_query_def,
      forall_exists_index, and_imp]
    obtain ⟨h_ov, h⟩ := h
    obtain ⟨w_1, h_1⟩ := h2
    obtain ⟨left, right⟩ := h

    have h1 : var ∈ BoundedQuery.variablesInQuery q.query := by apply vars_in_query_def.mpr; use w_1
    have h2 : BoundedQuery.Realize q.query ov (λ x => .none) := by
      sorry

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
          apply query_realizeDom_vars h_ov
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
