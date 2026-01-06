import RelationalAlgebra.Equivalence.RAtoFOL.ProjectionDef
import RelationalAlgebra.FOL.RelabelProperties

open RM

/-- Function to handle conversion of all Relational Algebra query cases. -/
def ra_to_fol_query (dbs : String → Finset String) : RA.Query String String → FOL.Query dbs
  | .R rn => .R rn (FOL.outVar ∘ RelationSchema.fromIndex)
  | .s a b sq => .and (ra_to_fol_query dbs sq) (.tEq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query dbs sq) rs
  | .j sq1 sq2 => .and (ra_to_fol_query dbs sq1) (ra_to_fol_query dbs sq2)
  | .r f sq => (ra_to_fol_query dbs sq).relabel (Sum.inl ∘ f)
  | .u sq₁ sq₂ => .or (ra_to_fol_query dbs sq₁) (ra_to_fol_query dbs sq₂)
  | .d sq nq => .and (ra_to_fol_query dbs sq) (.not (ra_to_fol_query dbs nq))

/-- Theorem to show that the conversion maintains the schema. -/
theorem ra_to_fol_query_schema {dbs : String → Finset String} {raQ : RA.Query String String} (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query dbs raQ).schema = raQ.schema dbs := by
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
      rw [ra_to_fol_query, RA.Query.schema, projectQuery.schema_def (ra_to_fol_query dbs sq) rs ?_]
      simp_all only [forall_const]

    | r f sq ih => simp_all [ra_to_fol_query, FOL.BoundedQuery.relabel_schema]

    | s => simp_all [ra_to_fol_query]

    | _ => simp_all [ra_to_fol_query]
