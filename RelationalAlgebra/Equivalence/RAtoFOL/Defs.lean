import RelationalAlgebra.Equivalence.RAtoFOL.Operations
import RelationalAlgebra.FOL.QueryAux

open RM

def projectAttribute (folQ : FOL.Query) (rs : RelationSchema) (a' : Attribute) : Attribute ⊕ Fin ((folQ.attributesInQuery \ rs).card) :=
   ((RelationSchema.index? (folQ.attributesInQuery \ rs) a').map (Sum.inr)).getD (Sum.inl a')

@[simp]
theorem projectAttribute_eq {folQ rs x y} : projectAttribute folQ rs x = Sum.inl y → x = y := by
    simp [projectAttribute]
    have ⟨z, hz⟩ : ∃z : Option (Attribute ⊕ Fin (Finset.card (FOL.BoundedQuery.attributesInQuery folQ \ rs))),
      z = (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) x))
        := exists_apply_eq_apply (fun a ↦ a) (Option.map Sum.inr (RelationSchema.index? (FOL.BoundedQuery.attributesInQuery folQ \ rs) x))
    by_cases h : z.isSome
    . simp only [Option.isSome_iff_exists] at h
      intro a
      subst hz
      simp_all only [Option.map_eq_some', Sum.exists, reduceCtorEq, and_false, exists_false, exists_const,
        Sum.inr.injEq, exists_eq_right, false_or]
      obtain ⟨w, h⟩ := h
      simp_all only [Option.map_some', Option.getD_some, reduceCtorEq]
    . simp at h
      subst h
      rw [hz.symm]
      simp [Option.getD_none]

@[simp]
theorem projectAttribute_mem {folQ rs a'} (h : a' ∈ rs) : projectAttribute folQ rs a' = Sum.inl a' := by
    simp [projectAttribute]
    have z : (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) a')) =
      (Option.none : Option (Attribute ⊕ Fin (Finset.card (folQ.attributesInQuery \ rs))))
        := by simp_all only [RelationSchema.index?_none, Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, Option.map_eq_none']

    rw [z]
    simp

@[simp]
theorem projectAttribute_not_mem {folQ rs a'} (h : a' ∈ folQ.attributesInQuery) (h' : a' ∉ rs) :
  ∃x, projectAttribute folQ rs a' = Sum.inr x := by
    simp [projectAttribute]

    have ⟨x, z2⟩ : ∃x, (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) a')) =
      (Option.some (Sum.inr x) : Option (Attribute ⊕ Fin (Finset.card (folQ.attributesInQuery \ rs))))
        := by
          simp_all
          apply RelationSchema.index?_isSome_eq_iff.mp
          apply RelationSchema.index?_isSome
          simp_all only [Finset.mem_sdiff, not_false_eq_true, and_true]

    use x
    rw [z2]
    simp

def projectQuery (folQ : FOL.Query) (rs : RelationSchema) : FOL.Query :=
  (folQ.relabel (λ a' => (projectAttribute folQ rs a'))).exs

@[simp]
theorem projectQuery.def [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) (h : rs ⊆ folQ.attributesInQuery) : (projectQuery folQ rs).attributesInQuery = rs := by
  ext a
  apply Iff.intro
  · intro a_1
    simp [FOL.BoundedQuery.attributesInQuery, projectQuery] at a_1
    obtain ⟨w, h_1⟩ := a_1
    obtain ⟨left, right⟩ := h_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only [projectAttribute_mem]
    . have z := projectAttribute_not_mem left h
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    simp_all [FOL.BoundedQuery.attributesInQuery, projectQuery]
    use a
    apply And.intro
    · exact h a_1
    · exact projectAttribute_mem a_1

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (ra_to_fol_query_def sq dbs).and (.eq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query_def sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query_def sq1 dbs) (ra_to_fol_query_def sq2 dbs)
  | .r f sq => (ra_to_fol_query_def sq dbs).relabel (Sum.inl ∘ f)

@[simp]
theorem ra_to_fol_query_schema [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) :
  (ra_to_fol_query_def raQ dbs).safeAttributes = raQ.schema dbs := by
    induction raQ
    all_goals simp_all [FOL.BoundedQuery.safeAttributes, ra_to_fol_query_def]
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
      simp_all only [FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.safeAttributes,
        FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, RA.Query.isWellTyped]
      simp_all [FOL.outVar, ← ra_to_fol_query_schema]
      obtain ⟨left, left_1, left_2, right⟩ := h
      have z1 := FOL.BoundedQuery.safeAtts_sub_attributesInQuery_mem (ra_to_fol_query_def sq dbs) left_1
      have z2 := FOL.BoundedQuery.safeAtts_sub_attributesInQuery_mem (ra_to_fol_query_def sq dbs) left_2
      simp_all [FOL.BoundedQuery.attributesInQuery]
      apply Finset.union_subset_iff.mpr
      simp_all only [Finset.singleton_subset_iff, and_self]

    case p rs sq ih =>
      simp [RA.Query.isWellTyped] at h
      obtain ⟨left, right⟩ := h
      simp_all [FOL.outVar, ← ra_to_fol_query_schema, FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.safeAttributes, projectQuery, FOL.BoundedQuery.attributesInQuery]
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
