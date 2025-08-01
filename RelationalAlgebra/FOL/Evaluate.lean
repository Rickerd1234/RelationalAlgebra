import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

namespace FOL

-- Evaluation logic
def VariableAssignmentToTuple {dbs : DatabaseSchema} (q : EvaluableQuery dbs) (ov : Attribute →. Value) : Tuple
  := (λ att => ((q.outFn att).bind ov))

theorem realize_relation_dom [folStruc] {n ov iv var} (q : BoundedQuery n)
  (h1 : var ∈ q.variablesInQuery) (h2 : q.Realize ov iv)
  : (ov var).Dom := by
    induction q with
    | R dbs rn h =>
      simp_all [BoundedQuery.variablesInQuery, BoundedQuery.toFormula, Relations.boundedFormula, BoundedFormula.Realize]
      have ⟨dbi, h3⟩ := folStruc_apply_RelMap h2
      have h4 := (dbi.relations rn).validSchema
      obtain ⟨w, h_1⟩ := h1
      obtain ⟨left, right⟩ := h3
      subst left
      have h5 := (dbi.schema rn).fromIndex_mem w
      have h6 := (arityToTuple_dom right).mpr h5
      simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def]
      have h7 : h w = (outVar var) := by
        unfold varFinsetLeft at *
        split at h_1
        next x i heq =>
          simp_all only [realize_var, Sum.elim_inl, Finset.mem_singleton]
          subst h_1
          rfl
        next x _i heq => simp_all only [realize_var, Sum.elim_inr, Finset.not_mem_empty]
        next x l _f ts heq => exact False.elim (folStruc_empty_fun _f)
      simp_all only
      exact h6
    -- | eq t₁ t₂ =>
    --   simp_all [BoundedQuery.variablesInQuery, BoundedQuery.toFormula, BoundedFormula.Realize, inVar]
    | and q1 q2 q1_ih q2_ih =>
      simp only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_inf] at h2
      simp only [BoundedQuery.variablesInQuery, Finset.union_empty, Finset.mem_union, BoundedFormula.freeVarFinset, BoundedQuery.toFormula] at h1
      obtain ⟨left, right⟩ := h2
      aesop
    | ex qs qs_ih =>
      simp_all only [BoundedQuery.Realize, BoundedQuery.variablesInQuery, BoundedQuery.toFormula, BoundedFormula.realize_ex, BoundedFormula.freeVarFinset]
      aesop

def EvaluableQuery.schema {dbs : DatabaseSchema} (q : EvaluableQuery dbs) : RelationSchema :=
  q.outFn.Dom.toFinset

def EvaluableQuery.evaluateT [folStruc]  {dbi : DatabaseInstance} (q : EvaluableQuery dbi.schema) : Set Tuple :=
{t |
  ∃ov, q.query.Realize dbi ov ∧ t = VariableAssignmentToTuple q ov
}

@[simp]
theorem realize_query_dom {ov : Attribute →. Value} {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi.schema) :
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
            -- next x t₁ t₂ heq => aesop
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
              -- next x_1 sq t₁ t₂ => aesop
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

theorem EvaluableQuery.evaluate_dom {dbi : DatabaseInstance} [folStruc] (q : EvaluableQuery dbi.schema) : ∀ t : Tuple, t ∈ EvaluableQuery.evaluateT q → t.Dom = q.schema := by
  simp [EvaluableQuery.evaluateT]
  intro t ov h
  by_cases h2 : q.query.Realize dbi ov
  . intros; simp_all only [realize_query_dom]
  . simp_all only

def EvaluableQuery.evaluate (dbi : DatabaseInstance) [folStruc] (q : EvaluableQuery dbi.schema)
  : RelationInstance := ⟨q.schema, q.evaluateT, q.evaluate_dom⟩
