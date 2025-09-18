import RelationalAlgebra.Equivalence.RAtoFOL.Relation
import RelationalAlgebra.Equivalence.RAtoFOL.Selection
import RelationalAlgebra.Equivalence.RAtoFOL.Projection
import RelationalAlgebra.Equivalence.RAtoFOL.Join
import RelationalAlgebra.Equivalence.RAtoFOL.Rename

open RM

@[simp]
theorem ra_to_fol_evalT.FOL_evaluateT (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) :
  t ∈ (ra_to_fol_query raQ dbi.schema).evaluateT dbi ↔ (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    simp_all only [FOL.Query.evaluateT, FOL.Query.RealizeDom.def, Set.mem_setOf_eq]

-- @TODO: Split this over multiple smaller proofs
theorem ra_to_fol_evalT.mp {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t → t ∈ RA.Query.evaluateT dbi raQ := by
    induction raQ with
    | R rn => exact R_def.mp
    | s a b p sq ih => exact s_def.mp h ih

    | p rs sq ih =>
      intro t
      simp only [RA.Query.isWellTyped.p_def, ra_to_fol_query, projectQuery.def, Nat.add_zero,
        FOL.Query.RealizeDom.def, FOL.BoundedQuery.schema.exs_def, FOL.BoundedQuery.relabel_schema,
        Finset.coe_pimage, RA.Query.evaluateT.p_def, projectionT, Set.mem_setOf_eq, and_imp] at ⊢ h
      intro a_2 a_3
      obtain ⟨left, right⟩ := h
      have h_rs : ↑rs ⊆ t.Dom := by sorry
      use t.restrict h_rs
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema, and_imp,
        forall_const]
      apply And.intro
      · sorry
      · intro a
        apply And.intro
        · intro a_1
          sorry
        · intro a_1
          sorry

    | j q₁ q₂ ih₁ ih₂ => exact j_def.mp h ih₁ ih₂

    | r f q ih => sorry

theorem ra_to_fol_evalT.mpr {raQ dbi} [struc : FOL.folStruc dbi] (h : RA.Query.isWellTyped dbi.schema raQ) :
  ∀t, t ∈ RA.Query.evaluateT dbi raQ → (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t := by
    induction raQ with
    | R rn => exact R_def.mpr h
    | s a b p sq ih => exact s_def.mpr h ih

    | p rs sq ih =>
      intro t h_RA_eval
      have t_Dom : t.Dom = rs := by
        exact RA.Query.evaluate.validSchema (.p rs sq) h t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.p rs sq) dbi.schema)
          (by simp_all)

      simp only [ra_to_fol_query]
      simp_all only [RA.Query.isWellTyped.p_def, RA.Query.evaluateT.p_def, projectionT,
        Set.mem_setOf_eq, forall_const]
      simp_all only [projectQuery.def, Nat.add_zero]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema]
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := h_RA_eval
      obtain ⟨hw, right_1⟩ := h

      have z := (ih w hw)
      have w_Dom : w.Dom = sq.schema dbi.schema := by
        exact RA.Query.evaluate.validSchema sq left w hw

      sorry

    | j q₁ q₂ ih₁ ih₂ => exact j_def.mpr h ih₁ ih₂

    | r f q ih =>
      intro t h_RA_eval
      apply
        FOL.Query.Realize.imp_RealizeDom_if_t_Dom_sub_schema
          (ra_to_fol_query (.r f q) dbi.schema)
          (by simp_all [RA.Query.evaluate.validSchema (.r f q) h t h_RA_eval])

      simp only [ra_to_fol_query]
      simp_all only [FOL.Query.RealizeDom.def, ra_to_fol_query.isWellTyped, ra_to_fol_query_schema,
        RA.Query.isWellTyped.r_def, RA.Query.evaluateT.r_def, renameT, exists_eq_right',
        Set.mem_setOf_eq, forall_const, and_self, implies_true]
      obtain ⟨left, right⟩ := h
      sorry

theorem ra_to_fol_evalT.mem (dbi : DatabaseInstance) [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema):
  ∀t, (ra_to_fol_query raQ dbi.schema).RealizeDom dbi t ↔ t ∈ raQ.evaluateT dbi := by
    intro t
    apply Iff.intro
    . exact ra_to_fol_evalT.mp h_ra_wt t
    . exact ra_to_fol_evalT.mpr h_ra_wt t

theorem ra_to_fol_eval {dbi} [struc : FOL.folStruc dbi] (raQ : RA.Query) (h_ra_wt : raQ.isWellTyped dbi.schema) :
  (ra_to_fol_query raQ dbi.schema).evaluate dbi = raQ.evaluate dbi h_ra_wt := by
    simp [RA.Query.evaluate, FOL.Query.evaluate]
    simp_all
    ext t
    simp_all only [ra_to_fol_evalT.FOL_evaluateT]
    exact ra_to_fol_evalT.mem dbi raQ h_ra_wt t

theorem ra_to_fol {dbi} [FOL.folStruc dbi] (raQ : RA.Query) (h : raQ.isWellTyped dbi.schema) :
  ∃folQ : FOL.Query, folQ.evaluate dbi = raQ.evaluate dbi h := by
    use ra_to_fol_query raQ dbi.schema
    exact ra_to_fol_eval raQ h


theorem fol_to_ra {dbi} [FOL.folStruc dbi] (folQ : FOL.Query) (h : folQ.isWellTyped dbi.schema) :
  ∃raQ : RA.Query, ∃(h' : raQ.isWellTyped dbi.schema), raQ.evaluate dbi h' = folQ.evaluate dbi := by sorry
