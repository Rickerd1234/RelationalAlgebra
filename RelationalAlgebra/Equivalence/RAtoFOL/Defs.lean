import RelationalAlgebra.Equivalence.RAtoFOL.Operations
import RelationalAlgebra.FOL.QueryAux

open RM

def projectQuery (folQ : FOL.Query) (rs : RelationSchema) : FOL.Query :=
  (folQ.relabel (λ a' => ((RelationSchema.index? (folQ.variablesInQuery \ rs) a').map (Sum.inr)).getD (Sum.inl a'))).exs

-- @TODO: for negative select add (λ q => ite (pos) q (.not q)) to .s

noncomputable def ra_to_fol_query_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : FOL.Query :=
  match raQ with
  | .R rn => .R dbs rn (FOL.outVar ∘ (dbs rn).fromIndex)
  | .s a b pos sq => (ra_to_fol_query_def sq dbs).relabel (λ a' => Sum.inl (ite (a' = b) a a'))
  | .p rs sq => projectQuery (ra_to_fol_query_def sq dbs) rs
  | .j sq1 sq2 => .and (ra_to_fol_query_def sq1 dbs) (ra_to_fol_query_def sq2 dbs)
  | .r f sq => (ra_to_fol_query_def sq dbs).relabel (Sum.inl ∘ f)

noncomputable def ra_to_fol_outFn_def [FOL.folStruc] (raQ : RA.Query) (dbs : DatabaseSchema) : Attribute →. Attribute :=
  match raQ with
  | .R rn => PFun.res id (dbs rn)
  | .s a b pos sq => λ a' => (ra_to_fol_outFn_def sq dbs) (ite (a' = b) a a')
  | .p rs sq => λ a => ite (a ∈ rs) ((ra_to_fol_outFn_def sq dbs) a) Part.none
  | .j sq1 sq2 => λ a => ite (a ∈ sq1.schema dbs) (ra_to_fol_outFn_def sq1 dbs a) (ra_to_fol_outFn_def sq2 dbs a)
  | .r f sq => (ra_to_fol_outFn_def sq dbs) ∘ f.invFun

theorem ra_to_fol_outFn_eq_schema [FOL.folStruc] {raQ : RA.Query} {dbs} (h : raQ.isWellTyped dbs) :
  (ra_to_fol_outFn_def raQ dbs).Dom = raQ.schema dbs := by
    induction raQ
    all_goals (
      simp [RA.Query.isWellTyped] at h
      simp_all [ra_to_fol_outFn_def, RA.Query.schema]
    )
    case R rn => rfl
    case s a b pos sq ih =>
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      ext a
      simp_all only [Set.mem_setOf_eq, Finset.mem_coe]
      apply Iff.intro
      · intro a_2
        split at a_2
        next h =>
          subst h
          simp_all only
        next h => simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
      · intro a_2
        split
        next h =>
          subst h
          simp_all only
          simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        next h => simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
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
        next h => simp_all only [true_or]
        next h =>
          simp_all only [RelationSchema.index?_none]
          simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
      · intro a_1
        cases a_1 with
        | inl h =>
          simp_all only [↓reduceIte]
          simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
        | inr h_1 =>
          split
          next h => simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
          next h =>
            simp_all only [RelationSchema.index?_none]
            simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
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

open FirstOrder Language

noncomputable def ra_to_fol_def [FOL.folStruc] {dbs} (raQ : RA.Query) (h : raQ.isWellTyped dbs) : FOL.EvaluableQuery dbs := ⟨
  ra_to_fol_query_def raQ dbs,
  ra_to_fol_outFn_def raQ dbs,
  by
    apply Fintype.ofFinset (raQ.schema dbs)
    exact fun x ↦ Iff.symm (ra_to_fol_outFn_schema_mem_iff h)
  ,
  by
    induction raQ
    all_goals (
      simp [RA.Query.isWellTyped] at h
      simp_all [ra_to_fol_query_def, ra_to_fol_outFn_def, FOL.BoundedQuery.variablesInQuery, FOL.BoundedQuery.toFormula]
    )
    case R rn =>
      simp [Relations.boundedFormula, BoundedFormula.freeVarFinset, Term.varFinsetLeft, FOL.outVar, PFun.res, PFun.ran, PFun.restrict]
      ext v
      simp_all only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
      apply Iff.intro
      · intro a
        use (dbs rn).index a
        simp_all only [RelationSchema.fromIndex_index_eq]
      · intro a
        obtain ⟨w, h_1⟩ := a
        subst h_1
        simp_all only [RelationSchema.fromIndex_mem]
    case s a b pos sq ih =>
      sorry
    all_goals sorry
⟩
