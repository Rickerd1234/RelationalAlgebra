import RelationalAlgebra.Equivalence.RAtoFOL.Operations
import RelationalAlgebra.FOL.QueryAux

open RM

def projectQuery (folQ : FOL.Query) (rs : RelationSchema) : FOL.Query :=
  (folQ.relabel (λ a' => ((RelationSchema.index? (folQ.attributesInQuery \ rs) a').map (Sum.inr)).getD (Sum.inl a'))).exs

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (ra_to_fol_query_def sq dbs).and (.eq (FOL.outVar a) (FOL.outVar b))
  | .p rs sq => projectQuery (ra_to_fol_query_def sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query_def sq1 dbs) (ra_to_fol_query_def sq2 dbs)
  | .r f sq => (ra_to_fol_query_def sq dbs).relabel (Sum.inl ∘ f)

noncomputable def ra_to_fol_outFn_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : Attribute →. Attribute :=
  match raQ with
  | .R rn => PFun.res id (dbs rn)
  | .s _ _ _ sq => ra_to_fol_outFn_def sq dbs
  | .p rs sq => λ a => ite (a ∈ rs) (ra_to_fol_outFn_def sq dbs a) Part.none
  | .j sq1 sq2 => λ a => ite (a ∈ sq1.schema dbs) (ra_to_fol_outFn_def sq1 dbs a) (ra_to_fol_outFn_def sq2 dbs a)
  | .r f sq => (ra_to_fol_outFn_def sq dbs) ∘ f.invFun

theorem ra_to_fol_query.isWellTyped [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) (h : raQ.isWellTyped dbs) :
  (ra_to_fol_query_def raQ dbs).isWellTyped := by
    induction raQ
    all_goals (
      simp_all [FOL.BoundedQuery.isWellTyped, ra_to_fol_query_def, FOL.BoundedQuery.safeAttributes, FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, RA.Query.isWellTyped, projectQuery, FOL.outVar]
      try aesop?
      try sorry
    )

theorem ra_to_fol_outFn_eq_schema [FOL.folStruc] {raQ : RA.Query} {dbs} (h : raQ.isWellTyped dbs) :
  (ra_to_fol_outFn_def raQ dbs).Dom = raQ.schema dbs := by
    induction raQ
    all_goals (
      simp [RA.Query.isWellTyped] at h
      simp_all [ra_to_fol_outFn_def, RA.Query.schema]
    )
    case R rn => rfl
    case p rs sq ih =>
      ext a
      simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro a_1
        split at a_1
        next h => simp_all only
        next h => simp_all only [RelationSchema.index?_none, Part.not_none_dom]
      · intro a_1
        have z : a ∈ (ra_to_fol_outFn_def sq dbs).Dom := by aesop
        simp_all only [Finset.mem_coe, Set.mem_setOf_eq, ↓reduceIte]
        simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
    case j sq1 sq2 ih1 ih2 =>
      ext a
      simp_all [ih1, ih2]
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro a_1
        split at a_1
        all_goals simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
      · intro a_1
        cases a_1
        all_goals (
          split
          all_goals simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        )
    case r f sq ih =>
      simp_all [renameSchema, Set.ext_iff]
      intro a
      obtain ⟨left, right⟩ := h
      apply Iff.intro
      · intro h'
        apply Exists.intro
        · apply And.intro
          · exact h'
          · simp_all only [f_inv_id]
      · intro h
        obtain ⟨w, h⟩ := h
        obtain ⟨left_1, right_1⟩ := h
        subst right_1
        simp_all only [inv_f_id_apply]

theorem ra_to_fol_outFn_schema_mem_iff [FOL.folStruc] {att : Attribute} {raQ : RA.Query} {dbs} (h : raQ.isWellTyped dbs) :
  att ∈ (ra_to_fol_outFn_def raQ dbs).Dom ↔ att ∈ raQ.schema dbs := by
    simp only [ra_to_fol_outFn_eq_schema, Finset.mem_coe, h]

theorem ra_to_fol_outFn_ran_from_schema [FOL.folStruc] {raQ : RA.Query} {dbs} (h : raQ.isWellTyped dbs) :
  x ∈ (ra_to_fol_outFn_def raQ dbs).ran ↔ ∃y ∈ (raQ.schema dbs), x ∈ (ra_to_fol_outFn_def raQ dbs) y := by
    simp only [PFun.ran]
    simp [← ra_to_fol_outFn_schema_mem_iff h]
    apply Iff.intro
    · intro a
      obtain ⟨w, h_1⟩ := a
      use w
      apply And.intro
      · use x
      · simp_all [← Part.eq_some_iff]
    · intro a
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      obtain ⟨w_1, h_1⟩ := left
      use w

-- @TODO: See if these are required/useful
-- instance ra_to_fol_outFn_def_Decidable_Dom {raQ : RA.Query} {dbs} [FOL.folStruc] (x : Attribute) (h : raQ.isWellTyped dbs)
--   : Decidable (ra_to_fol_outFn_def raQ dbs x).Dom
--   := by
--     simp only [Part.dom_iff_mem, ← PFun.mem_dom]
--     rw [ra_to_fol_outFn_schema_mem_iff h]
--     exact Finset.decidableMem x (raQ.schema dbs)

instance ra_to_fol_outFn_def_Fintype_Dom {raQ : RA.Query} {dbs} [FOL.folStruc] (h : raQ.isWellTyped dbs)
  : Fintype (ra_to_fol_outFn_def raQ dbs).Dom
  := by
    rw [ra_to_fol_outFn_eq_schema h]
    exact FinsetCoe.fintype (raQ.schema dbs)

@[simp]
theorem ra_to_fol_query.attributesInQuery_R [FOL.folStruc] :
  (ra_to_fol_query_def (.R rn) dbs).attributesInQuery = dbs rn := by
    simp only [FOL.BoundedQuery.attributesInQuery, ra_to_fol_query_def, FOL.BoundedQuery.toFormula,
      FirstOrder.Language.Relations.boundedFormula,
      FirstOrder.Language.BoundedFormula.freeVarFinset.eq_3, Function.comp_apply]
    ext a
    simp_all only [Finset.mem_biUnion, Finset.mem_univ, true_and, FOL.outVar]
    simp_all only [FirstOrder.Language.Term.varFinsetLeft, Finset.mem_singleton]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      subst h
      simp_all only [RelationSchema.fromIndex_mem]
    · intro a_1
      use RelationSchema.index a_1
      simp_all only [RelationSchema.fromIndex_index_eq]

-- @TODO: Verify this definition on paper
@[simp]
theorem ra_to_fol_query.attributesInQuery_s [FOL.folStruc] {a b x pos dbs} {sq : RA.Query}
  (h : (RA.Query.s a b pos sq).isWellTyped dbs)
  (h2 : (ra_to_fol_outFn_def sq dbs).ran = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq dbs)) :
    x ∈ (ra_to_fol_query_def (.s a b pos sq) dbs).attributesInQuery ↔ x ∈ (ra_to_fol_outFn_def sq dbs).ran := by
      sorry

-- @TODO: Verify this definition on paper
@[simp]
theorem ra_to_fol_query.attributesInQuery_p [FOL.folStruc] {rs dbs x} {sq : RA.Query}
  (h : (RA.Query.p rs sq).isWellTyped dbs)
  (h2 : (ra_to_fol_outFn_def sq dbs).ran = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq dbs)) :
    x ∈ (ra_to_fol_query_def (.p rs sq) dbs).attributesInQuery ↔ x ∈ rs := by
      simp [ra_to_fol_query_def, projectQuery]
      have := ra_to_fol_outFn_def_Fintype_Dom h.1
      have z : (ra_to_fol_outFn_def sq dbs).ran.toFinset = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq dbs)
        := by simp_all only [Finset.toFinset_coe]
      rw [z.symm]
      simp_all only [Finset.toFinset_coe]
      apply Iff.intro
      · intro a
        sorry
      · intro a
        sorry

-- @TODO: Verify this definition on paper
@[simp]
theorem ra_to_fol_query.attributesInQuery_j [FOL.folStruc] {dbs x} {sq₁ sq₂ : RA.Query}
  (h : (RA.Query.j sq₁ sq₂).isWellTyped dbs)
  (h2 : (ra_to_fol_outFn_def sq₁ dbs).ran = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq₁ dbs))
  (h3 : (ra_to_fol_outFn_def sq₂ dbs).ran = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq₂ dbs)) :
    x ∈ (ra_to_fol_query_def (.j sq₁ sq₂) dbs).attributesInQuery ↔ x ∈ (ra_to_fol_outFn_def sq₁ dbs).ran ∪ (ra_to_fol_outFn_def sq₂ dbs).ran := by
      simp_all [FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, ra_to_fol_query_def]

-- @TODO: Verify this definition on paper
@[simp]
theorem ra_to_fol_query.attributesInQuery_r [FOL.folStruc] {dbs x f} {sq : RA.Query}
  (h : (RA.Query.r f sq).isWellTyped dbs)
  (h2 : (ra_to_fol_outFn_def sq dbs).ran = FOL.BoundedQuery.attributesInQuery (ra_to_fol_query_def sq dbs)) :
    x ∈ (ra_to_fol_query_def (.r f sq) dbs).attributesInQuery ↔ x ∈ (ra_to_fol_outFn_def sq dbs).ran.image f := by
      simp_all [FOL.BoundedQuery.attributesInQuery, FOL.BoundedQuery.toFormula, ra_to_fol_query_def]

open FirstOrder Language

noncomputable def ra_to_fol_def [FOL.folStruc] {dbs} (raQ : RA.Query) (h : raQ.isWellTyped dbs) : FOL.EvaluableQuery dbs := ⟨
  ra_to_fol_query_def raQ dbs,
  ra_to_fol_outFn_def raQ dbs,
  Fintype.ofFinset (raQ.schema dbs) (fun x ↦ Iff.symm (ra_to_fol_outFn_schema_mem_iff h))
  ,
  by
    induction raQ

    case R rn =>
      simp [ra_to_fol_outFn_def, PFun.ran, PFun.res, PFun.restrict]

    case s a' b pos sq ih =>
      ext a
      simp
      rw [ra_to_fol_query.attributesInQuery_s h]
      . rw [ra_to_fol_outFn_ran_from_schema h, ra_to_fol_outFn_ran_from_schema h.1]
        simp_all [ra_to_fol_outFn_def, RA.Query.schema, RA.Query.isWellTyped, ra_to_fol_outFn_ran_from_schema]
      . have z2 := Finset.ext_iff.mp (ih h.1)
        ext y
        simp_all only [Set.mem_toFinset, Finset.mem_coe]

    case p rs sq ih =>
      ext a'
      simp
      rw [ra_to_fol_query.attributesInQuery_p h]
      . rw [ra_to_fol_outFn_ran_from_schema h]
        simp_all only [RA.Query.isWellTyped, RA.Query.schema, ra_to_fol_outFn_def, forall_true_left]
        sorry
      . have z2 := Finset.ext_iff.mp (ih h.1)
        ext y
        simp_all only [Set.mem_toFinset, Finset.mem_coe]

    case j q₁ q₂ ih₁ ih₂ =>
      ext a'
      simp
      rw [ra_to_fol_query.attributesInQuery_j h]
      . rw [ra_to_fol_outFn_ran_from_schema h]
        simp [ra_to_fol_outFn_def, ra_to_fol_outFn_ran_from_schema h.1, ra_to_fol_outFn_ran_from_schema h.2]
        apply Iff.intro
        · intro a
          obtain ⟨w, h_1⟩ := a
          split at h_1
          next h_2 =>
            apply Or.inl
            use w
            simp_all only [true_or, true_and, and_self]
          next h_2 =>
            apply Or.inr
            use w
            simp_all only [false_or, and_self]
        · intro a
          cases a with
          | inl h_1 =>
            obtain ⟨w, h_1⟩ := h_1
            use w
            simp_all only [true_or, ↓reduceIte, and_self]
          | inr h_2 =>
            obtain ⟨w, h_1⟩ := h_2
            use w
            split
            next h_2 => sorry
            next h_2 => simp_all
      . have z2 := Finset.ext_iff.mp (ih₁ h.1)
        ext y
        simp_all only [Set.mem_toFinset, Finset.mem_coe]
      . have z2 := Finset.ext_iff.mp (ih₂ h.2)
        ext y
        simp_all only [Set.mem_toFinset, Finset.mem_coe]

    case r f sq ih =>
      ext a'
      simp
      rw [ra_to_fol_query.attributesInQuery_r h]
      . rw [ra_to_fol_outFn_ran_from_schema h]
        simp [ra_to_fol_outFn_def, ra_to_fol_outFn_ran_from_schema h.1]
        sorry
      . have z2 := Finset.ext_iff.mp (ih h.1)
        ext y
        simp_all only [Set.mem_toFinset, Finset.mem_coe]
  ,
  ra_to_fol_query.isWellTyped raQ dbs h
⟩
