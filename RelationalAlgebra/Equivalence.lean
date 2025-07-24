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

theorem ra_to_fol [FOL.folStruc] {dbi} (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.EvaluableQuery dbi, raQ.evaluate dbi h = folQ.evaluate := by
    induction raQ with
    | R rn => sorry

    | s a b posEq sq ih =>
      simp_all [RA.Query.evaluate, RA.Query.evaluateT, RA.Query.isWellTyped, RA.Query.schema, selectionT, FOL.EvaluableQuery.evaluate, FOL.EvaluableQuery.schema, FOL.EvaluableQuery.evaluateT]
      simp [RA.Query.isWellTyped] at h
      simp_all only [forall_const]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := ih
      obtain ⟨left_1, right_1⟩ := h
      simp_all only [Set.mem_setOf_eq]

      use ra_to_fol_s w a b posEq

      sorry

    | p rs sq ih => sorry

    | j sq1 sq2 ih1 ih2 => sorry

    | r f sq ih =>
      simp_all [RA.Query.evaluate, RA.Query.evaluateT, RA.Query.isWellTyped, RA.Query.schema, renameT, FOL.EvaluableQuery.evaluate, FOL.EvaluableQuery.schema, FOL.EvaluableQuery.evaluateT]
      simp [RA.Query.isWellTyped] at h
      simp_all only [forall_const]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := ih
      obtain ⟨left_1, right_1⟩ := h
      simp_all only [Set.mem_setOf_eq]

      use ra_to_fol_r w f right

      simp only [renameSchema]
      apply And.intro
      . ext t : 1
        simp_all only [Finset.mem_image, Set.mem_toFinset, PFun.mem_dom, Function.comp_apply]
        apply Iff.intro
        · intro a_1
          obtain ⟨w_1, h⟩ := a_1
          obtain ⟨left_2, right_2⟩ := h
          obtain ⟨w_2, h⟩ := left_2
          subst right_2
          simp_all only [ra_to_fol_r, Function.comp_apply, inv_f_id_apply]
          apply Exists.intro w_2 h
        · intro ⟨w_1, h⟩
          apply Exists.intro
          · apply And.intro (Exists.intro w_1 h)
            · simp_all only [f_inv_id]
      . ext t
        simp_all only [Set.mem_setOf_eq]
        apply Iff.intro
        · intro a
          obtain ⟨ov, h⟩ := a
          obtain ⟨left_2, right_2⟩ := h
          unfold FOL.VariableAssignmentToTuple at *
          use ov
          simp_all only [true_and, ra_to_fol_r]
          ext a v
          simp_all only [Part.mem_bind_iff]
          simp_all only [Function.comp_apply]
          apply Iff.intro
          · intro a_1
            sorry
          · intro a_1
            obtain ⟨w_2, h⟩ := a_1
            obtain ⟨left_3, right_3⟩ := h
            sorry
        · intro a
          obtain ⟨w_1, h⟩ := a
          obtain ⟨left_2, right_2⟩ := h
          subst right_2
          unfold FOL.VariableAssignmentToTuple
          apply Exists.intro
          · apply And.intro left_2
            · ext a b : 1
              simp_all only [ra_to_fol_r, Function.comp_apply, inv_f_id_apply, Part.mem_bind_iff]


theorem fol_to_ra [FOL.folStruc] {dbi} (folQ : FOL.EvaluableQuery dbi) :
  ∃raQ : RA.Query, (h : raQ.isWellTyped dbi.schema) → raQ.evaluate dbi h = folQ.evaluate := by sorry
