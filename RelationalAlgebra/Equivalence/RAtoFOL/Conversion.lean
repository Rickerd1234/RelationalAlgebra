import RelationalAlgebra.Equivalence.RAtoFOL.ProjectionDef
import RelationalAlgebra.FOL.Properties

open RM

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (.tEq (ra_to_fol_query sq dbs) (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query sq1 dbs) (ra_to_fol_query sq2 dbs)
  | .r f sq => (ra_to_fol_query sq dbs).relabel (Sum.inl ∘ f)

theorem ra_to_fol_query_schema.def (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) (h' : (ra_to_fol_query raQ dbs).isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    induction raQ
    case R rn =>
      ext a
      simp_all [ra_to_fol_query, Finset.mem_singleton,
        Set.mem_toFinset, Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨w, h⟩
        subst h
        exact RelationSchema.fromIndex_mem w
      · intro a_1
        use RelationSchema.index a_1
        exact Eq.symm (RelationSchema.fromIndex_index_eq a_1)

    case p rs sq sq_ih =>
      ext a
      have z : (ra_to_fol_query sq dbs).isWellTyped dbs := by
        simp only [ra_to_fol_query] at h'
        exact projectQuery.isWellTyped_def (ra_to_fol_query sq dbs) rs h'
      obtain ⟨left, right⟩ := h
      rw [← sq_ih left z] at right
      rw [ra_to_fol_query, RA.Query.schema_p, projectQuery.schema_def (ra_to_fol_query sq dbs) rs right]


    case r f sq ih =>
      have z : (ra_to_fol_query sq dbs).isWellTyped dbs :=
        FOL.BoundedQuery.relabel_isWellTyped_sumInl f h.2.1 (ra_to_fol_query sq dbs) h'
      simp_all [ra_to_fol_query, FOL.BoundedQuery.relabel_schema]

    all_goals simp_all [ra_to_fol_query]

@[simp]
theorem ra_to_fol_query.isWellTyped (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).isWellTyped dbs := by
    induction raQ
    all_goals simp_all [RA.Query.isWellTyped, ra_to_fol_query, ra_to_fol_query_schema.def]

    case r f q q_ih =>
      exact FOL.BoundedQuery.relabel_isWellTyped (Sum.inl ∘ f) (Function.Injective.comp Sum.inl_injective h.2.1) (ra_to_fol_query q dbs) q_ih

theorem ra_to_fol_query_schema (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    refine ra_to_fol_query_schema.def raQ dbs h (ra_to_fol_query.isWellTyped raQ dbs h)
