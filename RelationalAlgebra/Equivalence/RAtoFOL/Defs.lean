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
theorem ra_to_fol_query_schema [struc : FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) (h' : (ra_to_fol_query raQ dbs).isWellTyped) :
  (ra_to_fol_query raQ dbs).schema = raQ.schema dbs := by
    induction raQ
    case R rn =>
      ext a
      simp_all [ra_to_fol_query, FOL.outVar, FirstOrder.Language.Term.varFinsetLeft, Finset.mem_singleton,
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
      have z : (ra_to_fol_query sq dbs).isWellTyped := by
        simp only [ra_to_fol_query] at h'
        exact projectQuery.isWellTyped_def (ra_to_fol_query sq dbs) rs h'
      simp [sq_ih h.1 z, h.2, ra_to_fol_query, projectAttribute]
      simp_all
      simp_all only
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h_1⟩ := a_1
        obtain ⟨left_1, right_1⟩ := h_1
        simp_all only [true_and, dite_not]
        split at right_1
        next h_1 =>
          simp_all only [FOL.BoundedQuery.isWellTyped.schema_eq_attributesInQuery, forall_const,
            RA.Query.isWellTyped.p_def, and_self, Sum.inl.injEq]
        next h_1 => simp_all only [reduceCtorEq]
      · intro a_1
        use a
        simp_all only [not_true_eq_false, and_false, ↓reduceDIte, and_true]
        exact right a_1


    case r f sq ih =>
      obtain ⟨left, right⟩ := h
      have z : (ra_to_fol_query sq dbs).isWellTyped :=
        FOL.BoundedQuery.relabel_isWellTyped_sumInl f right (ra_to_fol_query sq dbs) h'
      simp_all [ra_to_fol_query, FOL.BoundedQuery.isWellTyped.schema_eq_attributesInQuery]

    all_goals simp_all [ra_to_fol_query]

@[simp]
theorem ra_to_fol_query.isWellTyped [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query raQ dbs).isWellTyped := by
    induction raQ
    case R dbs rn => exact h

    case s q a b pos sq ih =>
      simp_all [RA.Query.isWellTyped, ra_to_fol_query,
        FOL.outVar, Finset.union_subset_iff]
      rw [← ra_to_fol_query_schema] at h
      . simp_all only [FOL.BoundedQuery.isWellTyped.schema_eq_attributesInQuery, and_self]
      . simp_all only
      . simp_all only

    case p rs sq ih =>
      simp_all only [RA.Query.isWellTyped, ← ra_to_fol_query_schema, ra_to_fol_query,
        projectQuery, FOL.BoundedQuery.isWellTyped.exs_def, FOL.BoundedQuery.relabel_isWellTyped]

    case j q₁ q₂ q₁_ih q₂_ih =>
      simp_all [RA.Query.isWellTyped, ra_to_fol_query,]

    case r f q q_ih =>
      simp_all only [RA.Query.isWellTyped, ra_to_fol_query,
        FOL.BoundedQuery.relabel_isWellTyped]
