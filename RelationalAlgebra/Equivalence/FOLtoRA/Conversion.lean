import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.Disjoint
import RelationalAlgebra.Equivalence.FOLtoRA.FreshAtts
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.Operators
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.RA.EquivRules

open RM FOL FirstOrder Language

variable {μ : Type}

@[simp]
def toPrenex (q : FOL.BoundedQuery dbs n) : (fol dbs).BoundedFormula String n :=
  q.toFormula.toPrenex

@[simp]
theorem toPrenex.freeVarFinset_def {q : FOL.Query dbs} : (toPrenex q).freeVarFinset = q.toFormula.freeVarFinset := by
  simp


theorem toRA.isWellTyped_def_IsAtomic {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsAtomic) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA q rs brs hn).isWellTyped dbs := by
      induction hq with
      | equal t₁ t₂ =>
        simp [Term.bdEqual, toRA, adom.isWellTyped_def]
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂
        split_ands
        all_goals(
          simp [Term.bdEqual] at h'
          simp [adom.schema_def, TermtoAtt]
          rename_i inst_1
          simp_all only [nonempty_subtype]
          obtain ⟨w, h_1⟩ := inst_1
          cases k₁ with
          | inl val =>
            cases k₂ with
            | inl
              val_1 =>
              simp_all only [Term.varFinsetLeft, Finset.singleton_union, Finset.union_insert]
              grind
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.empty_union, Finset.singleton_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
          | inr val_1 =>
            cases k₂ with
            | inl
              val =>
              simp_all only [Term.varFinsetLeft, Finset.singleton_union,
                Finset.union_insert, Finset.empty_union]
              simp_all [FRan, FRanS, Finset.insert_subset_iff]
              try simp_all [Set.subset_def]
            | inr
              val_2 =>
              simp_all only [Term.varFinsetLeft, Finset.empty_union]
              simp [FRan, FRanS] at *
              try simp_all [Set.subset_def]
        )
      | rel R ts =>
        simp [Relations.boundedFormula, BoundedFormula.freeVarFinset] at h'
        cases R with
        | R rn => simp [Relations.boundedFormula, toRA, relToRA.isWellTyped_def]

theorem toRA.isWellTyped_def_IsQF [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsQF) (h' : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card):
    (toRA q rs brs hn).isWellTyped dbs := by
      induction hq with
      | falsum => simp_all [toRA, adom.isWellTyped_def, adom.schema_def]
      | of_isAtomic h_at => exact isWellTyped_def_IsAtomic h_at h' hn
      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rename_i q₁ q₂
        rw [toRA]
        simp only [RA.Query.isWellTyped, RA.Query.schema]
        simp at h'
        have : q₁.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := by grind
        have : q₂.freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs := Finset.union_subset_right h'
        simp_all [adom.isWellTyped_def, adom.schema_def, toRA.schema_def]

theorem toRA.isWellTyped_def_IsPrenex {q : (fol dbs).BoundedFormula String n}
  (hq : q.IsPrenex) (h' : q.freeVarFinset ⊆ rs) (h'' : q.freeVarFinset ∩ brs = ∅) (hn : n + depth q < brs.card)
  [Fintype (adomRs dbs)] [Nonempty (adomRs dbs)] :
    (toRA q (rs ∪ FRan (FreeMap n brs)) brs hn).isWellTyped dbs := by
      induction hq with
      | of_isQF h_qf => exact isWellTyped_def_IsQF h_qf (by grind) (by grind)
      | all =>
        simp [toRA]
        simp at hn
        rename_i inst_1 n_1 φ h_1 h_ih

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by rw [FreeMap.FRan_union_add_one (by grind)]

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        exact Finset.union_subset_union_right (FreeMap.FRan_sub_add_one (by grind))

      | ex =>
        simp [toRA]
        rename_i inst_1 n_1 φ h_1 h_ih
        simp at h' h'' hn

        have wt := h_ih h' h'' (by grind)
        have sch : (rs ∪ (FRan (FreeMap n_1 brs) ∪ FRan (FreeMap (n_1 + 1) brs))) = (rs ∪ FRan (FreeMap (n_1 + 1) brs)) := by rw [FreeMap.FRan_union_add_one (by grind)]

        simp only [adom.isWellTyped_def, adom.schema_def, toRA.schema_def, true_and, and_true, *]
        exact Finset.union_subset_union_right (FreeMap.FRan_sub_add_one (by grind))


theorem toRA.evalT_def_IsAtomic [Nonempty μ] [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hq : q.IsAtomic) [Fintype (adomRs dbi.schema)] (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card)
  (hdisj : disjointSchema brs q) (hdef : default ∉ rs) :
    (toRA q rs brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | equal t₁ t₂ => exact equal_def h hn
      | rel R ts =>
        cases R with
        | R rn =>
          apply relToRA.evalT_def h hdef

          simp [Relations.boundedFormula, disjointSchema, Finset.ext_iff] at hdisj

          ext a
          simp_rw [Finset.mem_inter, Finset.mem_image, Finset.notMem_empty, iff_false, not_and,
            not_exists, not_and]
          intro ha a' ha'
          simp [renamer, RelationSchema.index?_eq_index_if_mem ha']
          have ⟨k, hk⟩ := Term.cases (ts (RelationSchema.index ha'))

          cases k
          all_goals (
            simp [TermtoAtt, hk]
            by_contra hc
            subst hc
            apply Set.not_notMem.mpr (Finset.mem_coe.mpr ha)
          )
          . apply (hdisj.1 _ (RelationSchema.index ha'))
            simp [hk]
          . apply (hdisj.2)
            exact FreeMap.mem_def (by grind)



theorem toRA.evalT_def_IsQF [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n}
  (hμ : ∀v, v ∈ dbi.domain) (hq : q.IsQF) [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)]
  (h : (q.freeVarFinset ∪ FRan (FreeMap n brs)) ⊆ rs) (hn : n + depth q < brs.card) (hdisj : disjointSchema brs q) (hdef : default ∉ rs) :
    (toRA q rs brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q rs brs t h} := by
      induction hq with
      | falsum => exact falsum_def
      | of_isAtomic h_at => exact toRA.evalT_def_IsAtomic h_at h hn hdisj hdef

      | imp h_qf₁ h_qf₂ ih₁ ih₂ =>
        rw [Finset.union_subset_iff, BoundedFormula.freeVarFinset, Finset.union_subset_iff] at h

        exact toRA.imp_def hμ hn
          (ih₁ (Finset.union_subset_iff.mpr ⟨h.1.1, h.2⟩) (by simp at hn; grind) (by simp at hdisj; exact ⟨hdisj.1.1, hdisj.2⟩))
          (ih₂ (Finset.union_subset_iff.mpr ⟨h.1.2, h.2⟩) (by simp at hn; grind) (by simp at hdisj; exact ⟨hdisj.1.2, hdisj.2⟩))

theorem toRA.evalT_def_IsPrenex [Nonempty μ] [folStruc dbi (μ := μ)] {q : (fol dbi.schema).BoundedFormula String n} [Fintype (adomRs dbi.schema)] [Nonempty ↑(adomRs dbi.schema)]
  (hμ : ∀v, v ∈ dbi.domain) (hq : q.IsPrenex) (h' : brs ∩ q.freeVarFinset = ∅) (hn : n + depth q < brs.card) (hdisj : disjointSchema brs q) (hdef : default ∉ q.freeVarFinset ∪ brs) :
    (toRA q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs hn).evaluateT dbi =
      {t | ∃h, RealizeDomSet q (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs t h} := by
        induction hq with
        | of_isQF hqf =>
          rename_i n' q
          have hdef' : default ∉ q.freeVarFinset ∪ FRan (FreeMap n' brs) := by
            simp at ⊢ hdef;
            apply And.intro hdef.1 (FreeMap.notMem_notMem_FRan ?_ hdef.2)
            grind
          exact evalT_def_IsQF hμ hqf (fun ⦃a⦄ a ↦ a) hn hdisj (hdef')

        | all hφ ih =>
          apply all_def hμ (by grind) ?_

          . simp [← Nat.add_assoc] at hn

            exact ih h' hn hdisj hdef

          . simp [Finset.eq_empty_iff_forall_notMem] at h'
            apply h'
            rw [FreeMap.fromIndex_brs_def]
            . simp
            . grind

        | ex hφ ih =>
          rename_i n' φ

          simp_rw [BoundedFormula.ex]
          apply not_def hμ
          have helper {n} : ∀ψ : (fol dbi.schema).BoundedFormula String n, (∼ψ).freeVarFinset = ψ.freeVarFinset := by simp
          rw [helper (φ.not.all)]

          apply all_def hμ (by simp at hn ⊢; grind) ?_ ∘ not_def hμ (by simp at hn ⊢; grind)

          . rw [helper φ]
            simp_rw [BoundedFormula.freeVarFinset, Finset.union_empty] at h' ⊢ hdef
            simp at hdisj
            simp [← Nat.add_assoc] at hn

            exact ih h' hn hdisj hdef

          . simp [Finset.eq_empty_iff_forall_notMem] at h'
            simp
            apply h'
            rw [FreeMap.fromIndex_brs_def]
            . simp
            . grind

-- Complete conversion
@[simp]
noncomputable def fol_to_ra_query (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Fintype ↑(adomAtts dbs)] : RA.Query String String :=
  toRA (toPrenex q) q.schema (FreshAtts (toPrenex q)) (by
    have ⟨k, hk⟩ := FreshAtts.card_def (toPrenex q)
    rw [hk]
    grind only
  )

@[simp]
theorem fol_to_ra_query.schema_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Fintype ↑(adomAtts dbs)] : (fol_to_ra_query q).schema dbs = q.schema := by
  rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, toRA.schema_def]

theorem fol_to_ra_query.isWellTyped_def (q : FOL.Query dbs) [Fintype (adomRs dbs)] [Fintype ↑(adomAtts dbs)] [Nonempty (adomRs dbs)] :
  (fol_to_ra_query q).isWellTyped dbs := by
    have : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan (FreeMap 0 (FreshAtts (toPrenex q))) = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp [FRan, FRanS]
    rw [fol_to_ra_query, BoundedQuery.schema, ← freeVarFinset_toPrenex, ← this]
    apply toRA.isWellTyped_def_IsPrenex ?_ ?_ ?_ ?_
    . simp [BoundedFormula.toPrenex_isPrenex]
    . simp
    . simp; grind
    . have ⟨k, hk⟩ := FreshAtts.card_def (toPrenex q)
      rw [hk]
      grind only

theorem fol_to_ra_query.evalT [folStruc dbi (μ := μ)] [Fintype (adomRs dbi.schema)] [Fintype ↑(adomAtts dbi.schema)] [Nonempty ↑(adomRs dbi.schema)] [Nonempty μ]
  (q : FOL.Query dbi.schema) (hμ : ∀v, v ∈ dbi.domain) (hdisj : disjointSchema (FreshAtts (toPrenex q)) q.toFormula) (hdef : default ∉ q.schema) :
    RA.Query.evaluateT dbi (fol_to_ra_query q) = FOL.Query.evaluateT dbi q ∩ {t | t.ran ⊆ dbi.domain} := by
      rw [FOL.Query.evaluateT, Set.ext_iff]
      intro t
      rw [@Set.mem_inter_iff]
      rw [Set.mem_setOf_eq, FOL.Query.RealizeMin.ex_def dbi q t, FOL.BoundedQuery.Realize]
      rw [fol_to_ra_query, BoundedQuery.schema]
      simp_rw [toPrenex]

      have hq := BoundedFormula.toPrenex_isPrenex (BoundedQuery.toFormula q)
      have helper : (BoundedQuery.toFormula q).toPrenex.freeVarFinset ∪ FRan (FreeMap 0 (FreshAtts (BoundedQuery.toFormula q).toPrenex))
        = (BoundedQuery.toFormula q).toPrenex.freeVarFinset := by simp [FRan, FRanS]
      rw [← freeVarFinset_toPrenex, ← helper, toRA.evalT_def_IsPrenex hμ hq ?_ _ ?_ ?_]

      rw [Set.mem_setOf_eq]
      simp only [BoundedFormula.realize_toPrenex, RealizeDomSet]
      simp_all only [freeVarFinset_toPrenex]

      have : ∀t' : String → μ, (t' ∘ (FreeMap 0 (FreshAtts (BoundedQuery.toFormula q).toPrenex))) = (default : Fin 0 → μ) := by intro t'; ext v; exact False.elim (Fin.elim0 v)
      simp_rw [this]
      . simp
      . simp; grind
      . exact ⟨(disjointSchemaL.toPrenex (BoundedQuery.toFormula q)).mpr hdisj.1, hdisj.2⟩
      . simp only [freeVarFinset_toPrenex, FreshAtts, FreshAttsAux, String.default_eq,
          Finset.union_singleton, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
          Set.mem_toFinset, true_or, not_true_eq_false, and_false, or_false]
        exact hdef
