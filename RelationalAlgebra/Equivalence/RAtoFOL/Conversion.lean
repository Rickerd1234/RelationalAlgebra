import RelationalAlgebra.Equivalence.RAtoFOL.ProjectionDef
import RelationalAlgebra.FOL.RelabelProperties

open RM FOL

variable {ρ α : Type} [LinearOrder α]

/-- Function to handle conversion of all Relational Algebra query cases. -/
def toFOL (dbs : ρ → Finset α) : RA.Query ρ α → FOL.Query dbs
  | .R rn => .R rn (freeVar ∘ RelationSchema.fromIndex)
  | .s a b sq => .and (toFOL dbs sq) (.tEq (freeVar a) (freeVar b))
  | .p rs sq => projectQuery (toFOL dbs sq) rs
  | .j sq₁ sq₂ => .and (toFOL dbs sq₁) (toFOL dbs sq₂)
  | .r f sq => (toFOL dbs sq).relabel (Sum.inl ∘ f)
  | .u sq₁ sq₂ => .or (toFOL dbs sq₁) (toFOL dbs sq₂)
  | .d sq nq => .and (toFOL dbs sq) (.not (toFOL dbs nq))

/-- Theorem to show that the conversion maintains the schema. -/
theorem toFOL.schema_def {dbs : ρ → Finset α} {raQ : RA.Query ρ α} (h : raQ.isWellTyped dbs) :
  (toFOL dbs raQ).schema = raQ.schema dbs := by
    induction raQ with
    | R rn =>
      ext a
      simp_all only [RA.Query.isWellTyped, toFOL, BoundedQuery.schema.R_def,
          Function.comp_apply, freeVar.def, FirstOrder.Language.Term.varFinsetLeft.eq_1,
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
      rw [toFOL, RA.Query.schema, projectQuery.schema_def (toFOL dbs sq) rs ?_]
      simp_all only [forall_const]

    | r f sq ih => simp_all only [RA.Query.isWellTyped, toFOL,
        BoundedQuery.relabel_schema, Function.comp_apply, Sum.getLeft?_inl, Part.coe_some,
        Finset.pimage_some, RA.Query.schema]

    | s => simp_all only [RA.Query.isWellTyped, toFOL, freeVar.def,
        BoundedQuery.schema.and_def, BoundedQuery.schema.tEq_def,
        FirstOrder.Language.Term.varFinsetLeft, Finset.union_singleton, Finset.union_insert,
        Finset.insert_eq_of_mem, RA.Query.schema]

    | _ => simp_all only [RA.Query.isWellTyped, toFOL, BoundedQuery.or,
        BoundedQuery.schema.not_def, BoundedQuery.schema.and_def, Finset.union_idempotent,
        RA.Query.schema]
