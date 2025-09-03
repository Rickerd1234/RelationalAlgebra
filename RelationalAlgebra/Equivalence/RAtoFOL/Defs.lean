import RelationalAlgebra.Equivalence.RAtoFOL.Operations
import RelationalAlgebra.FOL.Properties

open RM

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (ra_to_fol_query_def sq dbs).and (.tEq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query_def sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query_def sq1 dbs) (ra_to_fol_query_def sq2 dbs)
  | .r f sq => (ra_to_fol_query_def sq dbs).relabel (Sum.inl ∘ f)

@[simp]
theorem ra_to_fol_query_schema [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) :
  (ra_to_fol_query_def raQ dbs).schema = raQ.schema dbs := by
    induction raQ
    all_goals simp_all [FOL.BoundedQuery.schema, ra_to_fol_query_def]
    case R rn =>
      simp_all only [FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula,
        FirstOrder.Language.Relations.boundedFormula,
        FirstOrder.Language.BoundedFormula.freeVarFinset, Function.comp_apply, FOL.outVar,
        FirstOrder.Language.Term.varFinsetLeft.eq_1]
      ext a
      simp_all only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        subst h
        exact RelationSchema.fromIndex_mem w
      · intro a_1
        use RelationSchema.index a_1
        exact Eq.symm (RelationSchema.fromIndex_index_eq a_1)
    case p rs sq ih => sorry
    case r f sq ih => sorry

theorem ra_to_fol_query.isWellTyped [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query_def raQ dbs).isWellTyped := by
    induction raQ
    -- all_goals (
      -- simp_all only [FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.safeAttributes,
      --   FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, RA.Query.isWellTyped]
    -- )
    case s a b pos sq ih =>
      simp_all only [FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.schema,
        FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, RA.Query.isWellTyped]
      simp_all [FOL.outVar, ← ra_to_fol_query_schema]
      obtain ⟨left, left_1, left_2, right⟩ := h
      have z1 := FOL.BoundedQuery.schema_sub_attributesInQuery_mem (ra_to_fol_query_def sq dbs) left_1
      have z2 := FOL.BoundedQuery.schema_sub_attributesInQuery_mem (ra_to_fol_query_def sq dbs) left_2
      simp_all [FOL.BoundedQuery.attributesInQuery]
      apply Finset.union_subset_iff.mpr
      simp_all only [Finset.singleton_subset_iff, and_self]

    case p rs sq ih =>
      simp [RA.Query.isWellTyped] at h
      obtain ⟨left, right⟩ := h
      simp_all [FOL.outVar, ← ra_to_fol_query_schema, FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.schema, projectQuery, FOL.BoundedQuery.attributesInQuery]
      ext a
      simp_all only [Finset.mem_pimage, Part.mem_ofOption, Option.mem_def,
        Sum.getLeft?_eq_some_iff]
      rw [← ih] at right
      apply Iff.intro
      · intro a_1
        use a
        simp_all only [ra_to_fol_query_schema]
        apply And.intro
        · sorry
        · sorry
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left_1, right_1⟩ := h
        rw [← ih] at left_1
        sorry

    all_goals sorry

open FirstOrder Language

noncomputable def ra_to_fol_def [FOL.folStruc] {dbs} (raQ : RA.Query) (h : raQ.isWellTyped dbs) : FOL.EvaluableQuery := ⟨
  ra_to_fol_query_def raQ dbs,
  ra_to_fol_query.isWellTyped raQ dbs h
⟩
