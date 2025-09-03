import RelationalAlgebra.Equivalence.RAtoFOL.Operations
import RelationalAlgebra.FOL.Properties

open RM

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (.tEq (ra_to_fol_query sq dbs) (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query sq1 dbs) (ra_to_fol_query sq2 dbs)
  | .r f sq => (ra_to_fol_query sq dbs).relabel (Sum.inl ∘ f)

@[simp]
theorem ra_to_fol_query_schema [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) :
  (ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    induction raQ
    all_goals simp_all [FOL.BoundedQuery.schema, ra_to_fol_query]
    case R rn =>
      ext a
      simp_all only [FOL.outVar, FirstOrder.Language.Term.varFinsetLeft, Finset.mem_singleton,
        Set.mem_toFinset, Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨w, h⟩
        subst h
        exact RelationSchema.fromIndex_mem w
      · intro a_1
        use RelationSchema.index a_1
        exact Eq.symm (RelationSchema.fromIndex_index_eq a_1)
    case p rs sq ih => sorry
    case r f sq ih => sorry

@[simp]
theorem ra_to_fol_query.isWellTyped [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).isWellTyped := by
    induction raQ
    case R dbs rn => exact h

    case s q a b pos sq ih =>
      simp_all [RA.Query.isWellTyped, ← ra_to_fol_query_schema, ra_to_fol_query,
        FOL.outVar, Finset.union_subset_iff]

    case p rs sq ih =>
      simp_all only [RA.Query.isWellTyped, ← ra_to_fol_query_schema, ra_to_fol_query,
        projectQuery, FOL.BoundedQuery.isWellTyped.exs_def, FOL.BoundedQuery.relabel_isWellTyped]

    case j q₁ q₂ q₁_ih q₂_ih =>
      simp_all [RA.Query.isWellTyped, ra_to_fol_query,]

    case r f q q_ih =>
      simp_all only [RA.Query.isWellTyped, ra_to_fol_query,
        FOL.BoundedQuery.relabel_isWellTyped]
