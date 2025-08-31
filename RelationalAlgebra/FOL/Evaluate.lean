import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

namespace FOL


theorem realize_relation_dom_q [folStruc] {n t iv a} (q : BoundedQuery n)
  (h1 : a ∈ t.Dom) (h2 : q.Realize t iv)
  : a ∈ q.attributesInQuery := by
    simp_all only [PFun.mem_dom, query_realize_def]
    obtain ⟨w, h⟩ := h1
    induction q with
    | R dbs rn ta =>
      simp_all [BoundedQuery.toFormula]
      have ⟨dbi, h3⟩ := folStruc_apply_RelMap h2
      have h4 := (dbi.relations rn).validSchema
      -- obtain ⟨w, h_1⟩ := h1
      obtain ⟨left, right⟩ := h3
      subst left
      -- have h5 := (dbi.schema rn).fromIndex_mem w
      -- have h6 := (arityToTuple_dom right).mpr h5
      simp_all [FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, BoundedFormula.freeVarFinset, Relations.boundedFormula]
      have h' : a ∈ dbi.schema rn := by sorry
      use RelationSchema.index h'
      sorry
    | eq t₁ t₂ =>
      simp_all [BoundedQuery.toFormula, BoundedQuery.safeAttributes, BoundedQuery.attributesInQuery, Term.varFinsetLeft, BoundedFormula.Realize]
      unfold varFinsetLeft
      unfold Term.realize at h2
      sorry
    | and q1 q2 q1_ih q2_ih =>
      simp_all [BoundedQuery.toFormula, BoundedQuery.safeAttributes, BoundedQuery.attributesInQuery, Term.varFinsetLeft, BoundedFormula.Realize]
      obtain ⟨left, right⟩ := h2
      apply Or.inl (q1_ih left)
    | ex qs qs_ih =>
      simp_all [BoundedQuery.toFormula, BoundedQuery.safeAttributes, BoundedQuery.attributesInQuery, Term.varFinsetLeft, BoundedFormula.Realize]
      obtain ⟨w_1, h_1⟩ := h2
      apply @qs_ih
      · exact h_1

theorem realize_relation_dom_t [folStruc] {n t iv a} (q : BoundedQuery n)
  (h1 : a ∈ q.safeAttributes) (h2 : q.Realize t iv)
  : a ∈ t.Dom := by
    have h1' : a ∈ q.attributesInQuery := BoundedQuery.safeAtts_sub_attributesInQuery_mem q h1
    induction q with
    | R dbs rn h =>
      simp_all [BoundedQuery.attributesInQuery, BoundedQuery.toFormula, Relations.boundedFormula, BoundedFormula.Realize, BoundedQuery.safeAttributes]
      have ⟨dbi, h3⟩ := folStruc_apply_RelMap h2
      have h4 := (dbi.relations rn).validSchema
      obtain ⟨w, h_1⟩ := h1
      obtain ⟨left, right⟩ := h3
      subst left
      have h5 := (dbi.schema rn).fromIndex_mem w
      have h6 := (arityToTuple_dom right).mpr h5
      simp_all only [RelationSchema.fromIndex_mem, arityToTuple_def]
      have h7 : h w = (outVar a) := by
        unfold varFinsetLeft at *
        split at h_1
        next x i heq =>
          simp_all only [realize_var, Sum.elim_inl, Finset.mem_singleton]
          subst h_1
          rfl
        next x _i heq => simp_all only [realize_var, Sum.elim_inr, Finset.not_mem_empty]
        next x l _f ts heq => exact False.elim (folStruc_empty_fun _f)
      simp_all only
      exact Part.dom_iff_mem.mp h6
    | eq t₁ t₂ =>
      simp_all [BoundedQuery.attributesInQuery, BoundedQuery.toFormula, BoundedFormula.Realize, BoundedQuery.safeAttributes]
    | and q1 q2 q1_ih q2_ih =>
      simp only [BoundedQuery.Realize, BoundedQuery.toFormula, BoundedFormula.realize_inf] at h2
      simp only [BoundedQuery.attributesInQuery, Finset.union_empty, Finset.mem_union, BoundedFormula.freeVarFinset, BoundedQuery.toFormula] at h1'
      simp only [BoundedQuery.safeAttributes, BoundedQuery.attributesInQuery] at h1
      obtain ⟨left, right⟩ := h2
      simp_all [BoundedQuery.safeAtts_sub_attributesInQuery_mem]
      aesop
    | ex qs qs_ih =>
      simp_all only [BoundedQuery.Realize, BoundedQuery.attributesInQuery, BoundedQuery.toFormula, BoundedFormula.realize_ex, BoundedFormula.freeVarFinset]
      aesop

def EvaluableQuery.schema (q : EvaluableQuery) : RelationSchema :=
  q.query.attributesInQuery

def EvaluableQuery.evaluateT [folStruc] (q : EvaluableQuery) (dbi : DatabaseInstance) : Set Tuple :=
  {t | q.query.Realize dbi t}

@[simp]
theorem query_realize {t : Tuple} [folStruc] {q : EvaluableQuery} {dbi : DatabaseInstance} :
  q.query.Realize dbi t → q.query.toFormula.Realize t (λ _ => .none) := by
    intro h
    simp_all [Query.Realize, BoundedQuery.RealizeDom]
    have ⟨qq, hq⟩ : ∃ qq, q.query = qq := exists_eq'
    cases qq
    . simp_all only
    . simp_all only
    . simp_all only
    . simp_all [BoundedQuery.toFormula]
      obtain ⟨w, left, right⟩ := h.1
      apply Exists.intro
      · exact right

@[simp]
theorem realize_query_dom {t : Attribute →. Value} [folStruc] (q : EvaluableQuery) (dbi : DatabaseInstance) :
  q.query.Realize dbi t → t.Dom = q.schema := by
    intro h
    ext a
    simp_all only [Finset.mem_coe, EvaluableQuery.schema]
    apply Iff.intro
    · intro w
      have z := realize_relation_dom_q q.query w (query_realize h)
      simp_all only [is_well_typed_query_def]
    · intro h'
      simp [← is_well_typed_query_def] at h'
      exact realize_relation_dom_t q.query h' (query_realize h)

theorem EvaluableQuery.evaluate_dom [folStruc] (q : EvaluableQuery) (dbi : DatabaseInstance) :
  ∀ t : Tuple, t ∈ EvaluableQuery.evaluateT q dbi → t.Dom = q.schema :=
    λ _ h ↦ realize_query_dom q dbi h

def EvaluableQuery.evaluate [folStruc] (q : EvaluableQuery) (dbi : DatabaseInstance)
  : RelationInstance := ⟨q.schema, q.evaluateT dbi, q.evaluate_dom dbi⟩
