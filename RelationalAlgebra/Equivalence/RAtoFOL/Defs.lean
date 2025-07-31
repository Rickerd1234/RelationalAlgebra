import RelationalAlgebra.Equivalence.RAtoFOL.Operations

open RM

noncomputable def ra_to_fol_query_def [FOL.folStruc] (raQ : RA.Query) (dbi : DatabaseInstance) : FOL.Query :=
  match raQ with
  | .R rn => .R dbi rn (FOL.outVar ∘ att_to_var ∘ (dbi.schema rn).fromIndex)
  | .s a b pos sq => (ra_to_fol_query_def sq dbi) -- a b pos @TODO
  | .p rs sq => ra_to_fol_query_p (ra_to_fol_query_def sq dbi) rs
  | .j sq1 sq2 => sorry --ra_to_fol_query_j (ra_to_fol_query_def sq1 dbi) (ra_to_fol_def sq2 dbi) @TODO
  | .r f sq => ra_to_fol_query_r (ra_to_fol_query_def sq dbi) f

noncomputable def ra_to_fol_outFn_def [FOL.folStruc] (raQ : RA.Query) (dbi : DatabaseInstance) (h : raQ.isWellTyped dbi.schema) : Attribute →. FOL.Variable :=
  match raQ with
  | .R rn => PFun.res att_to_var (dbi.schema rn)
  | .s a b pos sq => ra_to_fol_outFn_def sq dbi (by simp_all [RA.Query.isWellTyped])
  | .p rs sq => ra_to_fol_outFn_p (ra_to_fol_outFn_def sq dbi (by simp_all [RA.Query.isWellTyped])) rs
  | .j sq1 sq2 => sorry -- @TODO
  | .r f sq => ra_to_fol_outFn_r (ra_to_fol_outFn_def sq dbi (by simp_all [RA.Query.isWellTyped])) f

theorem ra_to_fol_outFn_eq_schema [FOL.folStruc] {raQ : RA.Query} {dbi : DatabaseInstance} {h : raQ.isWellTyped dbi.schema} :
  (ra_to_fol_outFn_def raQ dbi h).Dom = raQ.schema dbi.schema := by
    induction raQ
    all_goals (
      simp [RA.Query.isWellTyped] at h
      simp_all [ra_to_fol_outFn_def, RA.Query.schema]
    )
    case R rn => rfl
    case p rs sq ih =>
      ext a
      simp_all only [PFun.mem_dom, Finset.mem_coe, ra_to_fol_outFn_p]
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        split at h
        next h_1 => simp_all only
        next h_1 => simp_all only [RelationSchema.index?_none, Part.not_mem_none]
      · intro a_1
        have z : a ∈ (ra_to_fol_outFn_def sq dbi left).Dom := by aesop
        simp only [Finset.mem_coe, ↓reduceIte, a_1]
        exact Part.dom_iff_mem.mp z
    case j sq1 sq2 ih1 ih2 => sorry -- @TODO
    case r sq f ih =>
      simp_all [ra_to_fol_outFn_r, renameSchema, Set.ext_iff]
      intro x
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro a
        apply Exists.intro
        · apply And.intro
          · exact a
          · simp_all only [f_inv_id]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        subst right_1
        simp_all only [inv_f_id_apply]

theorem ra_to_fol_outFn_schema_mem_iff [FOL.folStruc] {att : Attribute} {raQ : RA.Query} {dbi : DatabaseInstance} {h : raQ.isWellTyped dbi.schema} :
  att ∈ (ra_to_fol_outFn_def raQ dbi h).Dom ↔ att ∈ raQ.schema dbi.schema := by
    simp only [ra_to_fol_outFn_eq_schema, Finset.mem_coe]

open FirstOrder Language

noncomputable def ra_to_fol_def [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) : FOL.EvaluableQuery dbi := ⟨
  ra_to_fol_query_def raQ dbi,
  ra_to_fol_outFn_def raQ dbi h,
  by
    induction raQ
    all_goals (
      simp only [RA.Query.isWellTyped] at h
      simp_all only [ra_to_fol_outFn_def]
    )
    case R rn => sorry
    case s a b pos sq ih =>
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      cases b with
      | inl val => apply ih
      | inr val_1 => apply ih
    case p rs sq ih =>
      obtain ⟨left, right⟩ := h
      apply Fintype.ofFinset rs
      simp_all [ra_to_fol_outFn_p]
      intro x
      apply Iff.intro
      · intro a
        simp_all only [↓reduceIte, ← Part.dom_iff_mem]
        exact (ra_to_fol_outFn_schema_mem_iff).mpr (right a)
      · intro a
        obtain ⟨w, h⟩ := a
        split at h
        next h_1 => simp_all only
        next h_1 => simp_all only [RelationSchema.index?_none, Part.not_mem_none]
    all_goals sorry
  ,
  by
    induction raQ
    all_goals (
      simp_all [ra_to_fol_query_def, ra_to_fol_outFn_def, FOL.BoundedQuery.variablesInQuery, FOL.BoundedQuery.toFormula]
    )
    case R rn =>
      simp [Relations.boundedFormula, BoundedFormula.freeVarFinset, Term.varFinsetLeft, FOL.outVar, PFun.res, PFun.ran, PFun.restrict]
      ext v
      simp_all only [Finset.mem_coe, Part.mem_restrict, Part.mem_some_iff, Set.mem_toFinset, Set.mem_setOf_eq,
        Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
      apply Iff.intro
      · intro a
        obtain ⟨w, h_1⟩ := a
        obtain ⟨left, right⟩ := h_1
        subst right
        use RelationSchema.index left
        simp
      · intro a
        obtain ⟨w, h_1⟩ := a
        subst h_1
        use RelationSchema.fromIndex w
        apply And.intro (RelationSchema.fromIndex_mem w) rfl
    all_goals sorry
⟩
