import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate

open RM

def ra_to_fol_s {dbi} (w : FOL.EvaluableQuery dbi) (a : Attribute) (b : Attribute ⊕ Value) (posEq : Bool) : FOL.EvaluableQuery dbi := ⟨
  w.query,
  w.outFn,
  by sorry,
  by sorry
⟩

noncomputable def ra_to_fol_r {dbi} (w : FOL.EvaluableQuery dbi) (f : Attribute → Attribute) (h : f.Bijective) : FOL.EvaluableQuery dbi := ⟨
  w.query,
  w.outFn ∘ f.invFun,
  by
    have z : w.outFn.Dom.Finite := Set.toFinite w.outFn.Dom
    apply Set.Finite.fintype
    simp_all [PFun.Dom, Part.dom_iff_mem]
    apply Set.Finite.ofFinset (z.image f).toFinset
    intro x
    simp_all only [Set.Finite.mem_toFinset, Set.mem_image, Set.mem_setOf_eq]
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
  | .r f sq => ra_to_fol_r (ra_to_fol_def sq (by simp_all [RA.Query.isWellTyped])) f (by simp_all [RA.Query.isWellTyped])
  | _ => sorry

theorem ra_to_fol_eval [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  raQ.evaluate dbi h = (ra_to_fol_def raQ h).evaluate := by
    simp [FOL.EvaluableQuery.evaluate, RA.Query.evaluate, FOL.EvaluableQuery.schema]
    induction raQ with
    | r f sq ih =>
      simp only [RA.Query.isWellTyped] at h
      apply And.intro
      . simp_all only [RA.Query.schema, renameSchema]
        simp_all only [ra_to_fol_def, ra_to_fol_r]
        aesop
      . simp_all [RA.Query.evaluateT, renameT]
        simp_all [ra_to_fol_def, ra_to_fol_r, FOL.EvaluableQuery.evaluateT, FOL.VariableAssignmentToTuple]
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
          unfold FOL.VariableAssignmentToTuple at ⊢ right_2 right_1
          simp_all only [Function.comp_apply]
          ext a v
          simp_all only [Part.mem_bind_iff]
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
    | _ => sorry


theorem ra_to_fol [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.EvaluableQuery dbi, raQ.evaluate dbi h = folQ.evaluate := by
    use ra_to_fol_def raQ h
    simp [ra_to_fol_eval]


theorem fol_to_ra [FOL.folStruc] {dbi} (folQ : FOL.EvaluableQuery dbi) :
  ∃raQ : RA.Query, (h : raQ.isWellTyped dbi.schema) → raQ.evaluate dbi h = folQ.evaluate := by sorry
