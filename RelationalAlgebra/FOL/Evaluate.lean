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

      simp_all [BoundedQuery.variablesInQuery, RelationTermRestriction.outVars, outVar?, RelationTermRestriction.vars]
      obtain ⟨w, h⟩ := h1
      obtain ⟨left, right⟩ := h
      split at right
      next x x_1 =>
        simp_all only [Sum.getLeft?_eq_some_iff]
        subst right
        rw [@ran_mem] at left
        obtain ⟨w, h⟩ := left
        have z : w ∈ brtr.schema := by
          simp_all only [brtr_schema_dbi_def]
          rw [← @BoundedRelationTermRestriction.validSchema]
          simp_all only [Set.mem_toFinset, PFun.mem_dom, Part.mem_some_iff, exists_eq]
        have h3 := (folStruc.RelMap_R brtr.dbi brtr.name (fun i ↦ realize (Sum.elim ov iv) (getMap brtr i))).mpr h2


        have h4 : (ArityToTuple fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)).Dom = (brtr.dbi.relations brtr.name).schema := by
          apply (brtr.dbi.relations brtr.name).validSchema (ArityToTuple fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)) h3
        simp_all only [brtr_schema_dbi_def]
        have h5 : w ∈ PFun.Dom (ArityToTuple fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)) := by
          simp_all only [Finset.mem_coe]
          simp_all [DatabaseInstance.validSchema]
        apply Part.dom_iff_mem.mpr
        use ((ArityToTuple fun i ↦ realize (Sum.elim ov iv) (getMap brtr i)) w).get h5
        have ⟨w_1, h_1⟩ : ∃i, w = (brtr.dbi.schema brtr.name).fromIndex i := by
          simp_all only [← DatabaseInstance.validSchema]
          use RelationSchema.index h5
          simp_all only [RelationSchema.fromIndex_index_eq]

        subst h_1
        simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def]
        unfold getMap
        simp_all only [Part.get_some, realize_var, Sum.elim_inl]

        exact?
      next => simp_all only [imp_false, Sum.forall, reduceCtorEq]
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

def EvaluableQuery.schema {dbi : DatabaseInstance} (q : EvaluableQuery dbi) : RelationSchema :=
  q.outFn.Dom.toFinset

def EvaluableQuery.EvaluateTuples {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : Set Tuple :=
{t |
  ∃ov, q.query.Realize dbi ov ∧ t = VariableAssignmentToTuple q ov
}

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
          have ⟨hw, hz⟩ : ∃iv, BoundedQuery.Realize q.query ov iv := by
            unfold Query.Realize BoundedQuery.RealizeDom BoundedQuery.Realize BoundedQuery.toFormula at *
            simp_all only [Nat.reduceAdd, Part.coe_some]
            split
            next x brtr heq =>
              simp_all only [BoundedFormula.realize_rel]
              obtain ⟨left, right⟩ := h
              obtain ⟨left_1, right⟩ := right
              exact Exists.intro (fun x ↦ Part.none) left
            next x q1 q2 heq =>
              simp_all only [BoundedFormula.realize_inf]
              obtain ⟨left, right⟩ := h
              obtain ⟨left, right_1⟩ := left
              obtain ⟨left_1, right⟩ := right
              exact Filter.frequently_principal.mp fun a ↦ a left right_1
            next x q_1
              heq =>
              simp_all only [BoundedFormula.realize_ex, Nat.succ_eq_add_one, Nat.reduceAdd]
              obtain ⟨left, right⟩ := h
              obtain ⟨w, h⟩ := left
              obtain ⟨left, right⟩ := right
              obtain ⟨left_1, right_1⟩ := h
              split at right_1
              next x_1 brtr =>
                simp_all only [BoundedFormula.realize_rel]
                apply Exists.intro
                · apply Exists.intro
                  · exact right_1
              next x_1 q1 q2 =>
                simp_all only [BoundedFormula.realize_inf]
                obtain ⟨left_2, right_1⟩ := right_1
                simp_all [BoundedQuery.toFormula]
                apply Exists.intro
                · apply Exists.intro
                  · apply And.intro
                    on_goal 2 => {exact right_1
                    }
                    · simp_all only
              next x_1 q_1 =>
                simp_all only [BoundedFormula.realize_ex, Nat.succ_eq_add_one, Nat.reduceAdd]
                obtain ⟨w_1, h⟩ := right_1
                simp_all [BoundedQuery.toFormula]
                apply Exists.intro
                · apply Exists.intro
                  · apply Exists.intro
                    · exact h
          refine realize_relation_dom q.query ?_ hz
          . simp_all only [query_realize_def, vars_in_query_def]
            apply Exists.intro
            · exact h_1
      simp_all only [Part.get_some, Part.mem_some_iff, exists_eq]

theorem EvaluableQuery.evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi) : ∀ t : Tuple, t ∈ EvaluateTuples q → t.Dom = q.schema := by
  simp [EvaluateTuples]
  intro t ov h
  by_cases h2 : q.query.Realize dbi ov
  . intros; simp_all only [realize_query_dom]
  . simp_all only

def EvaluableQuery.Evaluate {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi)
  : RelationInstance := ⟨q.schema, q.EvaluateTuples, q.evaluate_dom⟩
