import RelationalAlgebra.Equivalence.RAtoFOL.ProjectionDef
import RelationalAlgebra.FOL.RelabelProperties

open RM

variable {ρ α : Type} [LinearOrder α]

/-- Function to handle conversion of all Relational Algebra query cases. -/
def ra_to_fol_query (dbs : ρ → Finset α) : RA.Query ρ α → FOL.Query dbs
  | .R rn => .R rn (FOL.outVar ∘ RelationSchema.fromIndex)
  | .s a b sq => .and (ra_to_fol_query dbs sq) (.tEq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query dbs sq) rs
  | .j sq₁ sq₂ => .and (ra_to_fol_query dbs sq₁) (ra_to_fol_query dbs sq₂)
  | .r f sq => (ra_to_fol_query dbs sq).relabel (Sum.inl ∘ f)
  | .u sq₁ sq₂ => .or (ra_to_fol_query dbs sq₁) (ra_to_fol_query dbs sq₂)
  | .d sq nq => .and (ra_to_fol_query dbs sq) (.not (ra_to_fol_query dbs nq))

/-- Theorem to show that the conversion maintains the schema. -/
theorem ra_to_fol_query_schema {dbs : ρ → Finset α} {raQ : RA.Query ρ α} (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query dbs raQ).schema = raQ.schema dbs := by
    induction raQ with
    | R rn =>
      ext a
      simp_all only [RA.Query.isWellTyped, ra_to_fol_query, FOL.BoundedQuery.schema.R_def,
          Function.comp_apply, FOL.outVar.def, FirstOrder.Language.Term.varFinsetLeft.eq_1,
          Finset.mem_singleton, Set.mem_toFinset, Set.mem_setOf_eq, RA.Query.schema]
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

    | r f sq ih => simp_all only [RA.Query.isWellTyped, ra_to_fol_query,
        FOL.BoundedQuery.relabel_schema, Function.comp_apply, Sum.getLeft?_inl, Part.coe_some,
        Finset.pimage_some, RA.Query.schema]

    | s => simp_all only [RA.Query.isWellTyped, ra_to_fol_query, FOL.outVar.def,
        FOL.BoundedQuery.schema.and_def, FOL.BoundedQuery.schema.tEq_def,
        FirstOrder.Language.Term.varFinsetLeft, Finset.union_singleton, Finset.union_insert,
        Finset.insert_eq_of_mem, RA.Query.schema]

    | _ => simp_all only [RA.Query.isWellTyped, ra_to_fol_query, FOL.BoundedQuery.or,
        FOL.BoundedQuery.schema.not_def, FOL.BoundedQuery.schema.and_def, Finset.union_idempotent,
        RA.Query.schema]
