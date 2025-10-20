import RelationalAlgebra.Equivalence.RAtoFOL.ProjectionDef
import RelationalAlgebra.FOL.RelabelProperties

open RM

noncomputable def ra_to_fol_query (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query dbs :=
  match raQ with
  | .R rn => .R rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b sq => .and (ra_to_fol_query sq dbs) (.tEq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query sq1 dbs) (ra_to_fol_query sq2 dbs)
  | .r f sq => (ra_to_fol_query sq dbs).relabel (Sum.inl ∘ f)
  | .u sq₁ sq₂ => .or (ra_to_fol_query sq₁ dbs) (ra_to_fol_query sq₂ dbs)
  | .d sq nq => .and (ra_to_fol_query sq dbs) (.not (ra_to_fol_query nq dbs))

theorem ra_to_fol_query_schema.def (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    induction raQ with
    | R rn =>
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

    | p rs sq sq_ih =>
      ext a
      obtain ⟨left, right⟩ := h
      rw [ra_to_fol_query, RA.Query.schema, projectQuery.schema_def (ra_to_fol_query sq dbs) rs ?_]
      simp_all only [forall_const]

    | r f sq ih => simp_all [ra_to_fol_query, FOL.BoundedQuery.relabel_schema]

    | s => simp_all [ra_to_fol_query, Finset.union_subset_iff]

    | _ => simp_all [ra_to_fol_query]

theorem ra_to_fol_query_schema (h : raQ.isWellTyped dbs) :
(ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    refine ra_to_fol_query_schema.def raQ dbs h
