import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate

open RM
def att_to_var : Attribute → FOL.Variable :=
  Nat.repr

def var_to_att : FOL.Variable → Attribute :=
  String.toNat!

theorem var_to_att_to_var_eq_id : var_to_att ∘ att_to_var = id := by
  sorry

def schema_to_inFn {n} (dbs : DatabaseSchema) (rn : RelationName) : Attribute →. FOL.Language.fol.Term (FOL.Variable ⊕ Fin n) :=
  PFun.res (FOL.outVar ∘ att_to_var) (dbs rn)

def ra_to_fol_R {dbi} (rn : RelationName) : FOL.EvaluableQuery dbi := ⟨
  (.R dbi rn (by aesop) : FOL.BoundedQuery (dbi.schema rn).card).exs, -- @TODO: Add outVar concept
  PFun.res att_to_var (dbi.schema rn),
  by
    apply Fintype.ofFinset (dbi.schema rn);
    simp_all [PFun.res]
  ,
  by
    simp_all [PFun.ran, FOL.BoundedQuery.variablesInQuery, FOL.RelationTermRestriction.outVars, FOL.RelationTermRestriction.vars, FOL.outVar?, att_to_var, schema_to_inFn, FOL.outVar, Finset.filterMap, PFun.res, PFun.restrict, Part.restrict]
    ext v
    simp_all only [Set.mem_toFinset, Set.mem_setOf_eq, Part.mem_mk_iff, Finset.mem_coe, exists_prop, Finset.mem_mk,
      Multiset.mem_filterMap, Finset.mem_val, exists_exists_and_eq_and]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      simp_all only [FOL.outVar?, Sum.getLeft?_inl, Option.some.injEq]
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
⟩

def ra_to_fol_s {dbi} (w : FOL.EvaluableQuery dbi) (a : Attribute) (b : Attribute ⊕ Value) (posEq : Bool) : FOL.EvaluableQuery dbi := ⟨
  w.query,
  w.outFn,
  by sorry,
  by sorry
⟩

theorem p_sub_query_proof {rs dbi} {w : FOL.EvaluableQuery dbi} (h : ↑rs ⊆ w.schema) : ↑rs ⊆ w.outFn.Dom := by simp_all [FOL.EvaluableQuery.schema]

def emptyRTR {n} (name : RelationName): FOL.RelationTermRestriction n := ⟨(λ _ => .none), name, (by apply Fintype.ofFinset ∅; simp_all)⟩

def freeVarRTR (name : RelationName) (rs : RelationSchema) (att : Attribute) (h : att ∈ rs.ordering) : FOL.RelationTermRestriction rs.card := ⟨
    (λ a => ite (a = att) ((rs.index? att).map FOL.inVar) (.none)),
    name,
    by
      apply Fintype.ofFinset {att}
      intro x
      simp_all only [Finset.mem_singleton, PFun.dom_mk, Set.mem_setOf_eq]
      apply Iff.intro
      · intro a
        subst a
        simp_all only [RelationSchema.ordering_mem, ↓reduceIte, Part.ofOption_dom, Option.isSome_map',
          RelationSchema.index?_isSome]
      · intro a
        split at a
        next h =>
          subst h
          simp_all only [Part.ofOption_dom, Option.isSome_map', RelationSchema.index?_isSome_eq_iff]
        next h => simp_all only [Part.not_none_dom]
⟩

def FOL.RelationTermRestriction.merge {n} (prev added : FOL.RelationTermRestriction n) : FOL.RelationTermRestriction n := ⟨
  λ a => ite (prev.inFn a).Dom (prev.inFn a) (added.inFn a),
  prev.name,
  by
    apply Fintype.ofFinset (prev.inFn.Dom.toFinset ∪ added.inFn.Dom.toFinset)
    intro x
    simp_all only [Finset.mem_union, Set.mem_toFinset, PFun.mem_dom, PFun.dom_mk, Set.mem_setOf_eq]
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        obtain ⟨w, h⟩ := h
        split
        next h_1 => simp_all only
        next h_1 => rw [Part.dom_iff_mem] at h_1; simp_all
      | inr h_1 =>
        obtain ⟨w, h⟩ := h_1
        split
        next h_1 => simp_all only
        next h_1 => rw [Part.dom_iff_mem]; use w
    · intro a
      split at a
      next h =>
        simp_all only
        rw [Part.dom_iff_mem] at a; simp_all
      next h => rw [Part.dom_iff_mem] at a; simp_all
⟩

-- Use ordering, otherwise we require comm and assoc for merge :(
def FOL.RelationTermRestriction.project {n} (rtr : FOL.RelationTermRestriction n) (rs : RelationSchema) : FOL.RelationTermRestriction rs.card :=
  rs.ordering.foldl (λ prev (a : Attribute) => dite (a ∈ rs.ordering) (λ h => FOL.RelationTermRestriction.merge (freeVarRTR rtr.name rs a h) prev) (λ _ => prev)) (emptyRTR rtr.name)

theorem FOL.RelationTermRestriction.merge_name {n} (prev added : FOL.RelationTermRestriction n) (h : prev.name = added.name)
  : (FOL.RelationTermRestriction.merge prev added).name = prev.name := by
    simp_all only
    exact h

theorem FOL.RelationTermRestriction.project_name {n} (rtr : FOL.RelationTermRestriction n) (rs : RelationSchema)
  : (FOL.RelationTermRestriction.project rtr rs).name = rtr.name := by
    simp_all [project]
    induction rs using Finset.induction with
    | empty => simp_all only [Finset.card_empty, Finset.not_mem_empty, ↓reduceDIte, List.foldl_fixed, emptyRTR]
    | insert h_new ih =>
      simp_all
      rename_i a s
      by_cases h : a ∈ s
      . sorry
      . sorry

def FOL.BoundedRelationTermRestriction.projectBRTR {n} (brtr : FOL.BoundedRelationTermRestriction n) (rs : RelationSchema) (h : n ≤ rs.card) : FOL.BoundedQuery n :=
  (FOL.BoundedQuery.R ⟨(⟨brtr.inFn, brtr.name, brtr.fintypeDom⟩ : RelationTermRestriction n).project rs, brtr.dbi, by simp_all [FOL.RelationTermRestriction.project]⟩).exs


def FOL.BoundedQuery.project {n} : FOL.BoundedQuery n → RelationSchema → FOL.BoundedQuery n
  | .R brtr, rs => brtr.projectBRTR rs (by sorry)
  | q, _ => q

def ra_to_fol_p {dbi} (w : FOL.EvaluableQuery dbi) (rs : RelationSchema) (h : ↑rs ⊆ w.schema) : FOL.EvaluableQuery dbi := ⟨
  w.query.project rs,
  w.outFn.restrict (p_sub_query_proof h),
  by
    apply Fintype.ofFinset rs
    intro x
    simp [FOL.EvaluableQuery.schema] at h
    simp_all only [PFun.mem_dom, PFun.mem_restrict, Finset.mem_coe, exists_and_left, iff_self_and]
    intro a
    have z : x ∈ w.outFn.Dom := by apply Set.mem_of_subset_of_mem h a
    simp_all only [PFun.mem_dom]
  ,
  by
    simp_all [PFun.ran, FOL.BoundedQuery.project]
    ext v
    sorry
⟩

noncomputable def ra_to_fol_r {dbi} (w : FOL.EvaluableQuery dbi) (f : Attribute → Attribute) (h : f.Bijective) : FOL.EvaluableQuery dbi := ⟨
  w.query,
  w.outFn ∘ f.invFun,
  by
    apply Fintype.ofFinset (w.outFn.Dom.toFinset.image f);
    intro x
    simp_all only [Finset.mem_image, Set.mem_toFinset, PFun.mem_dom, Function.comp_apply]
    apply Iff.intro
    · intro a
      obtain ⟨w_1, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      obtain ⟨w_2, h_1⟩ := left
      subst right
      simp_all only [inv_f_id_apply]
      apply Exists.intro w_2 h_1
    · intro a
      obtain ⟨w_1, h_1⟩ := a
      apply Exists.intro
      · apply And.intro (Exists.intro w_1 h_1)
        · simp_all only [f_inv_id]
  ,
  by
    rw [← w.varsInQuery]
    simp_all [PFun.ran]
    ext v
    simp_all only [Set.mem_setOf_eq]
    apply Iff.intro
    . intro a
      obtain ⟨w_1, h_1⟩ := a
      exact Exists.intro (Function.invFun f w_1) h_1
    . intro ⟨w_1, h_1⟩
      use f w_1
      simp_all only [inv_f_id_apply]
⟩

noncomputable def ra_to_fol_def [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) : FOL.EvaluableQuery dbi :=
  match raQ with
  | .R rn => ra_to_fol_R rn
  | .s a b pos sq => ra_to_fol_s (ra_to_fol_def sq (by simp_all [RA.Query.isWellTyped])) a b pos
  | .p rs sq => ra_to_fol_p (ra_to_fol_def sq (by simp_all [RA.Query.isWellTyped])) rs (by simp [RA.Query.isWellTyped] at h; aesop?)
  -- | .j sq1 sq2 => ra_to_fol_j (ra_to_fol_def sq1 (by simp_all [RA.Query.isWellTyped])) (ra_to_fol_def sq2 (by simp_all [RA.Query.isWellTyped])) sq1 sq2
  | .r f sq => ra_to_fol_r (ra_to_fol_def sq (by simp_all [RA.Query.isWellTyped])) f (by simp_all [RA.Query.isWellTyped])
  | _ => sorry

theorem ra_to_fol_eval [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  raQ.evaluate dbi h = (ra_to_fol_def raQ h).evaluate := by
    simp [FOL.EvaluableQuery.evaluate, RA.Query.evaluate, FOL.EvaluableQuery.schema]
    induction raQ
    all_goals (
      simp only [RA.Query.isWellTyped] at h
      simp_all only [FOL.EvaluableQuery.evaluateT, forall_true_left, RA.Query.schema, ra_to_fol_def, RA.Query.evaluateT]
    )
    case R rn =>
      apply And.intro
      . simp_all [ra_to_fol_R, PFun.res, PFun.restrict, PFun.Dom, Part.restrict]
      . simp_all [ra_to_fol_R]
        ext t
        simp_all only [Set.mem_setOf_eq]
        apply Iff.intro
        · intro ht
          use λ v => t (var_to_att v)
          apply And.intro
          · simp_all [FOL.Query.Realize]
            apply And.intro
            · sorry
            · apply And.intro
              · sorry
              · simp [PFun.ran]
          · unfold FOL.VariableAssignmentToTuple
            simp_all [PFun.res, PFun.restrict, Part.restrict, Part.bind]
            simp [← Function.comp_apply, var_to_att_to_var_eq_id]
            simp_all only [Function.comp_apply]
            ext a v
            simp_all only [Part.mem_assert_iff, Finset.mem_coe, exists_prop, iff_and_self]
            intro a_1
            rw [DatabaseInstance.validSchema]
            have hz : a ∈ t.Dom → a ∈ (dbi.relations rn).schema := by simp [(dbi.relations rn).validSchema t ht]
            apply hz
            apply (PFun.mem_dom t a).mpr
            use v
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left, right⟩ := h
          subst right
          sorry
    case s a b posEq sq ih =>
      apply And.intro
      . simp_all only [ra_to_fol_s, Set.toFinset_inj]
      . simp_all [ra_to_fol_s, selectionT]
        ext t
        simp_all only [Set.mem_setOf_eq]
        apply Iff.intro
        . intro a_1
          obtain ⟨left_3, right_2⟩ := a_1
          obtain ⟨w, h⟩ := left_3
          use w
          simp_all only [true_and]
          rfl
        . unfold FOL.VariableAssignmentToTuple at *

          intro a_1
          simp_all only [true_and]
          obtain ⟨left, right⟩ := h
          obtain ⟨left_1, right⟩ := right
          obtain ⟨left_2, right_1⟩ := ih
          obtain ⟨w, h⟩ := a_1
          obtain ⟨left_3, right_2⟩ := h
          subst right_2
          simp_all only
          cases b with
          | inl val =>
            simp_all only [selectionT.def_att]
            split
            next h =>
              subst h
              ext v
              simp_all only [Part.mem_bind_iff]
              apply Iff.intro
              · intro a_1
                obtain ⟨w_1, h⟩ := a_1
                obtain ⟨left_4, right_2⟩ := h
                sorry
              · intro a_1
                obtain ⟨w_1, h⟩ := a_1
                obtain ⟨left_4, right_2⟩ := h
                sorry
            next h =>
              simp_all only [Bool.not_eq_true]
              subst h
              apply Aesop.BuiltinRules.not_intro
              intro a_1
              sorry
          | inr val_1 =>
            simp_all only [selectionT.def_val]
            split
            next h =>
              subst h
              ext v
              simp_all only [Part.mem_bind_iff, Part.mem_some_iff]
              apply Iff.intro
              · intro a_1
                obtain ⟨w_1, h⟩ := a_1
                obtain ⟨left_4, right_2⟩ := h
                sorry
              · intro a_1
                subst a_1
                sorry
            next h =>
              simp_all only [Bool.not_eq_true]
              subst h
              apply Aesop.BuiltinRules.not_intro
              intro a_1
              sorry
    case r f sq ih =>
      apply And.intro
      . simp_all only [renameSchema, ra_to_fol_r]
        aesop
      . simp_all only [renameT, Set.mem_setOf_eq, exists_eq_right', ra_to_fol_r]
        ext t
        simp_all only [forall_true_left, Set.mem_setOf_eq]
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right_1⟩ := ih
        apply Iff.intro
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_2, right_2⟩ := h
          use w
          simp_all only [true_and]
          ext a v
          unfold FOL.VariableAssignmentToTuple at *
          simp_all only [Function.comp_apply, Part.mem_bind_iff]
          apply Iff.intro
          · intro a_1
            sorry
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            obtain ⟨left_3, right_3⟩ := h
            sorry
        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_2, right_2⟩ := h
          subst right_2
          unfold FOL.VariableAssignmentToTuple
          apply Exists.intro
          · apply And.intro
            · exact left_2
            · ext a b : 1
              simp_all only [Function.comp_apply, inv_f_id_apply, Part.mem_bind_iff]
    all_goals sorry


theorem ra_to_fol [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.EvaluableQuery dbi, raQ.evaluate dbi h = folQ.evaluate := by
    use ra_to_fol_def raQ h
    simp [ra_to_fol_eval]


theorem fol_to_ra [FOL.folStruc] {dbi} (folQ : FOL.EvaluableQuery dbi) :
  ∃raQ : RA.Query, (h : raQ.isWellTyped dbi.schema) → raQ.evaluate dbi h = folQ.evaluate := by sorry
