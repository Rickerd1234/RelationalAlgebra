import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Realize
import RelationalAlgebra.FOL.Properties
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

theorem realize_relation_dom_q[folStruc] {a dbi} {t : Tuple} (q : Query)
  (h1 : a ∈ t.Dom) (h2 : q.Realize dbi t) (h3 : q.isWellTyped)
  : a ∈ q.schema := by
    simp_all [PFun.mem_dom]
    obtain ⟨w, h⟩ := h1
    cases q with
    | R dbs rn ta =>
      sorry
      -- have ⟨dbi, h3⟩ := folStruc_apply_RelMap h2
      -- have h4 := (dbi.relations rn).validSchema
      -- -- obtain ⟨w, h_1⟩ := h1
      -- obtain ⟨left, right⟩ := h3
      -- subst left
      -- have h5 := (dbi.schema rn).fromIndex_mem w
      -- have h6 := (arityToTuple_dom right).mpr h5
      -- simp_all [FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, BoundedFormula.freeVarFinset, Relations.boundedFormula]
      -- have h' : a ∈ dbi.schema rn := by sorry
      -- use RelationSchema.index h'
    | tEq q t₁ t₂ =>
      sorry
      -- simp_all only [query_realize_tEq, query_realize_tEq_def, BoundedQuery.toFormula_tEq,
      --   BoundedQuery.isWellTyped.tEq_def, BoundedQuery.schema.tEq_def, Finset.not_mem_empty]
      -- obtain ⟨left, right⟩ := h2
      -- obtain ⟨left_1, right_1⟩ := h3
      -- obtain ⟨left, right_2⟩ := left
      -- obtain ⟨left_2, right⟩ := right
      -- obtain ⟨w_1, h_1⟩ := left_1
      -- obtain ⟨w_2, h_2⟩ := right_1
      -- obtain ⟨left_1, right_1⟩ := right_2
      -- subst h_1 h_2
      -- exact left_1
    | and q1 q2 =>
      sorry
      -- simp_all [BoundedQuery.toFormula, BoundedQuery.schema, BoundedQuery.attributesInQuery, Term.varFinsetLeft, BoundedFormula.Realize, BoundedQuery.RealizeDom, BoundedQuery.Realize, BoundedQuery.isWellTyped]
      -- aesop?
      -- obtain ⟨left, right⟩ := h2
      -- apply Or.inl (q1_ih left)
    | ex qs =>
      sorry
      -- simp_all [BoundedQuery.toFormula, BoundedQuery.schema, BoundedQuery.attributesInQuery, Term.varFinsetLeft, BoundedFormula.Realize]
      -- obtain ⟨w_1, h_1⟩ := h2
      -- apply @qs_ih
      -- · exact h_1

theorem realize_relation_dom_t [folStruc] {a dbi} {t : Tuple} (q : Query)
  (h1 : a ∈ q.schema) (h2 : q.Realize dbi t) (h3 : q.isWellTyped)
  : a ∈ t.Dom := by
    have h1' : a ∈ q.attributesInQuery := BoundedQuery.schema.sub_attributesInQuery_mem q h1
    cases q with
    | R dbs rn h =>
      simp_all [BoundedQuery.attributesInQuery, BoundedQuery.toFormula, BoundedQuery.RealizeDom, Relations.boundedFormula, BoundedFormula.Realize, BoundedQuery.schema]
      have ⟨dbi, h3⟩ := folStruc_apply_RelMap h2.1.1
      obtain ⟨w, h_1⟩ := h1
      obtain ⟨left, right⟩ := h3
      subst left
      have h5 := (dbi.schema rn).fromIndex_mem w
      have h6 := (arityToTuple_dom right).mpr h5
      use (ArityToTuple (fun i ↦ realize (Sum.elim t (λ _ ↦ Part.none)) (h i)) (RelationSchema.fromIndex w)).get h6
      have h7 : h w = (outVar a) := by
        unfold varFinsetLeft at *
        split at h_1
        next x i heq =>
          simp_all only [realize_var, Sum.elim_inl, Finset.mem_singleton]
          subst h_1
          rfl
        next x _i heq => simp_all only [realize_var, Sum.elim_inr, Finset.not_mem_empty]
        next x l _f ts heq => exact False.elim (folStruc_empty_fun _f)
      simp_all [outVar, Part.get_mem]
    | tEq q₁ t₁ t₂ =>
      aesop
      all_goals simp_all [BoundedQuery.attributesInQuery, BoundedQuery.toFormula, BoundedFormula.Realize, BoundedQuery.schema]
      all_goals sorry
    | and q1 q2 =>
      sorry
      -- simp only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_inf] at h2
      -- simp only [BoundedQuery.attributesInQuery, Finset.union_empty, Finset.mem_union, BoundedFormula.freeVarFinset, BoundedQuery.toFormula] at h1'
      -- simp only [BoundedQuery.schema, BoundedQuery.attributesInQuery] at h1
      -- obtain ⟨left, right⟩ := h2
      -- simp_all [BoundedQuery.schema.sub_attributesInQuery_mem]
      -- aesop
    | ex qs =>
      -- simp_all only [BoundedQuery.Realize, BoundedQuery.attributesInQuery, BoundedQuery.toFormula, BoundedFormula.realize_ex, BoundedFormula.freeVarFinset]
      sorry

def Query.evaluateT [folStruc] {q : FOL.Query} (dbi : DatabaseInstance) : Set Tuple :=
  {t | q.Realize dbi t}

@[simp]
theorem realize_query_dom {t : Attribute →. Value} [folStruc] {q : Query} (h_wt : q.isWellTyped) (dbi : DatabaseInstance) :
  q.Realize dbi t → t.Dom = q.schema := by
    intro h_rel
    ext a
    simp_all only [Finset.mem_coe]
    apply Iff.intro
    · intro h_dom
      exact realize_relation_dom_q q h_dom h_rel h_wt
    · intro h_schema
      exact realize_relation_dom_t q h_schema h_rel h_wt

theorem Query.evaluate_dom [folStruc] {q : Query} (h : q.isWellTyped) (dbi : DatabaseInstance) :
  ∀ t : Tuple, t ∈ q.evaluateT dbi → t.Dom = q.schema :=
    λ _ hx ↦ realize_query_dom h dbi hx

def Query.evaluate [folStruc] {q : Query} (h : q.isWellTyped) (dbi : DatabaseInstance)
  : RelationInstance := ⟨q.schema, q.evaluateT dbi, evaluate_dom h dbi⟩
