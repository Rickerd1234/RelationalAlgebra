import RelationalAlgebra.Equivalence.FOLtoRA.Adom
import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.Relation
import RelationalAlgebra.Equivalence.FOLtoRA.Term
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.RealizeProperties
import RelationalAlgebra.RA.EquivRules

/-
This file is responsible for all conversions except the Relation case, as well as all proofs for these cases.
The Relation case is handled in `Relation.lean`.
-/

open RM FOL FirstOrder Language

variable {μ : Type}

section toRA

variable {ρ α : Type} [LinearOrder α] [Inhabited α] [Inhabited ρ] [LinearOrder ρ] {dbs : ρ → Finset α} [Fintype (adomRs dbs)]

/--
Convert a `BoundedFormula α n` to a `RA.Query ρ α`.
The result is the RA representation of the FOL query, with schema `rs`.
`adom rs` is a cartesian product of any value for each attribute in `rs`, which restricts any query to the active domain of the database.
Requires the formula `f` to be in Prenex normal form to work as expected.
Requires `brs` to be distinct from `f.freeVarFinset` and `n + depth f < brs.card` to work properly.
Requires `f.freeVarFinset ⊆ rs` to work properly.
-/
def toRA
  (f : (fol dbs).BoundedFormula α n) (rs brs : Finset α) : RA.Query ρ α :=
    match f with
    -- `adom rs - adom rs`
    | .falsum => .d (adom dbs rs) (adom dbs rs)
    -- `σ (f t₁ = f t₂) adom rs`
    | .equal t₁ t₂ => .s (TermtoAtt brs t₁) (TermtoAtt brs t₂) (adom dbs rs)
    -- Handled in `Relation.lean`
    | .rel (.R rn) ts => relToRA ts rs brs
    -- `adom rs - (toRA f₁ rs - toRA f₂ rs)`
    | .imp f₁ f₂ => .d (adom dbs rs) (.d (toRA f₁ rs brs) (toRA f₂ rs brs))
    -- `adom rs - (π rs (adom rs' - toRA sf rs'))`
    --  where `rs'` is `rs` combined with all variables used to rename bound variables (`FRan (FreeMap (n + 1) brs))`).
    | .all sf => (adom dbs rs).d (.p rs ((adom dbs (rs ∪ FRan (FreeMap (n + 1) brs))).d (toRA sf (rs ∪ FRan (FreeMap (n + 1) brs)) brs)))

theorem toRA.schema_def :
    (toRA (dbs := dbs) φ rs brs).schema dbs = rs := by
  induction φ with
  | rel R ts =>
    cases R
    next n rn => simp [toRA, relToRA.schema_def]
  | _ => simp [toRA, adom.schema_def]

end toRA

variable {ρ α : Type} {dbi : DatabaseInstance ρ α μ} [LinearOrder α] [Inhabited α] [Inhabited μ]

theorem toRA.term_equal_def [folStruc dbi (μ := μ)] {t₁ t₂ : (fol dbi.schema).Term (α ⊕ Fin n)} {t : α →. μ} {rs : Finset α}
  (h : t.Dom = ↑rs) (h' : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs):
    t (TermtoAtt brs t₁) = t (TermtoAtt brs t₂) ↔
      (BoundedFormula.equal t₁ t₂).Realize (TupleToFun h) (TupleToFun h ∘ FreeMap n brs) := by
        have ⟨k₁, hk₁⟩ := Term.cases t₁
        have ⟨k₂, hk₂⟩ := Term.cases t₂
        subst hk₁ hk₂

        cases k₁
        all_goals (
          cases k₂
          all_goals (
            -- Rewrite ... ⊆ rs
            simp only [Term.bdEqual, BoundedFormula.freeVarFinset, Term.varFinsetLeft, Finset.insert_union, ← h,
              Finset.singleton_union, Finset.subset_iff, ← Finset.mem_coe, Finset.coe_insert, Set.mem_insert_iff,
              forall_eq_or_imp, Finset.empty_union, PFun.mem_dom, ← Part.dom_iff_mem] at h'

            -- Prepare for `TupleToFun.tuple_eq_iff`
            apply Iff.symm
            rw [TermtoAtt, TermtoAtt]
            simp only [BoundedFormula.Realize, Term.realize_var, Sum.elim_inl, Sum.elim_inr, Function.comp]

            -- Complete the proof
            apply TupleToFun.tuple_eq_iff h
            . simp_all only [Finset.mem_coe, FRan.mem_def]
            . simp_all only [Finset.mem_coe, FRan.mem_def]
          )
        )

/- To use computable `adom`, we require the following properties for `ρ` -/
variable [Inhabited ρ] [LinearOrder ρ]

/- Proof `toRA` evaluation for `Set` of tuples to be equivalent to `RealizeDomSet` for the distinct cases -/
theorem toRA.falsum_def [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] :
    (toRA (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs).evaluateT dbi =
      RealizeDomSet (BoundedFormula.falsum (L := fol dbi.schema) (n := n)) rs brs := by
        have : (RA.Query.evaluateT dbi (adom dbi.schema rs)) \ (RA.Query.evaluateT dbi (adom dbi.schema rs)) = ∅ := Set.diff_self
        simp_rw [toRA, RA.Query.evaluateT, differenceT, this]
        simp [RealizeDomSet, BoundedFormula.Realize]


theorem toRA.equal_def [Nonempty ↑(adomRs dbi.schema)] [Fintype ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] {t₁ t₂ : (fol dbi.schema).Term (α ⊕ Fin n)}
  (h : (t₁ =' t₂).freeVarFinset ∪ FRan (FreeMap n brs) ⊆ rs) :
    (toRA (t₁ =' t₂) rs brs).evaluateT dbi = RealizeDomSet (t₁ =' t₂) rs brs := by
      simp_rw [Term.bdEqual, toRA, RA.Query.evaluateT, selectionT]
      simp_rw [RealizeDomSet]

      rw [adom.complete_def]
      ext t
      simp_rw [Set.mem_setOf_eq, exists_and_right]

      apply Iff.intro
      . intro ⟨⟨w_1, h_2, h_3⟩, right⟩
        split_ands
        . use h_2
          apply (term_equal_def h_2 h).mp right
        . apply h_3
      . intro ⟨⟨w_1, h_2⟩, right⟩
        apply And.intro
        . apply And.intro ?_ (And.intro w_1 right)
          have ⟨v, hv⟩ : ∃v, v ∈ t.ran := by
            rw [Finset.subset_iff] at h
            simp [PFun.ran, exists_comm, ← PFun.mem_dom, w_1]
            have ⟨k, hk⟩ := Term.cases t₁
            cases k with
            | inl val =>
              use val
              apply h
              simp [hk, Term.bdEqual]
            | inr i =>
              cases n with
              | zero => apply Fin.elim0 i
              | succ n' =>
                use FreeMap (n' + 1) brs (Fin.last n')
                apply h
                simp
          simp [DatabaseInstance.domain, Set.subset_def] at right
          obtain ⟨rn, att, t, ht₁, ht₂⟩ := right v hv
          use rn
          simp [adomRs]
          apply And.intro
          . simp_rw [← dbi.validSchema, Finset.eq_empty_iff_forall_notMem, ← Finset.mem_coe,  ← (dbi.relations rn).validSchema t ht₁]
            simp_rw [PFun.mem_dom, not_exists, not_forall, not_not]
            use att, v
            exact Part.eq_some_iff.mp ht₂
          . use t
        . exact ((term_equal_def w_1 h).mpr h_2)

theorem toRA.imp_def [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)]
  (hμ : ∀v : μ, v ∈ dbi.domain)
  (ih₁ : (toRA (dbs := dbi.schema) q₁ rs brs).evaluateT dbi = RealizeDomSet q₁ rs brs)
  (ih₂ : (toRA (dbs := dbi.schema) q₂ rs brs).evaluateT dbi = RealizeDomSet q₂ rs brs) :
    (toRA (q₁.imp q₂) rs brs).evaluateT dbi = RealizeDomSet (q₁.imp q₂) rs brs := by
      ext t
      simp only [toRA, RA.Query.evaluateT, differenceT, adom.complete_def, Set.mem_diff, Set.mem_setOf_eq,
        not_and, not_not, RealizeDomSet, BoundedFormula.realize_imp, exists_and_right]
      simp_all only [nonempty_subtype, RealizeDomSet, Finset.coe_inj, exists_and_right,
        Set.mem_setOf_eq, and_true, and_imp, forall_exists_index, exists_true_left,
        TupleToFun.tuple_eq_self]
      apply Iff.intro
      · intro a_1
        simp_all only [implies_true, exists_const, and_self]
      · intro ⟨⟨w_1, h_1⟩, right⟩
        simp_all [Finset.coe_inj, TupleToFun.tuple_eq_self, implies_true, and_self]
        apply adom.exists_tuple_from_value hμ

theorem toRA.not_def [Nonempty ↑(adomRs dbi.schema)] [Fintype ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)]
  (hμ : ∀v : μ, v ∈ dbi.domain)
  (ih : (toRA (dbs := dbi.schema) q rs brs).evaluateT dbi = RealizeDomSet q rs brs) :
    (toRA q.not rs brs).evaluateT dbi = RealizeDomSet (q.not) rs brs := by
      exact imp_def hμ ih falsum_def

theorem toRA.all_def [Nonempty ↑(adomRs dbi.schema)] [folStruc dbi (μ := μ)] [Fintype ↑(adomRs dbi.schema)] {q : (fol dbi.schema).BoundedFormula α (n + 1)}
  (hμ : ∀v : μ, v ∈ dbi.domain) (hn : n + depth (∀'q) < brs.card) (h : (FreeMap (n + 1) brs) (Fin.last n) ∉ q.freeVarFinset)
  (ih : (toRA q (q.freeVarFinset ∪ FRan (FreeMap (n + 1) brs)) brs).evaluateT dbi = RealizeDomSet q (q.freeVarFinset ∪ FRan (FreeMap (n + 1) brs)) brs) :
    (toRA q.all (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs).evaluateT dbi = RealizeDomSet (q.all) (q.freeVarFinset ∪ FRan (FreeMap n brs)) brs := by
      simp only [toRA, RA.Query.evaluateT, Finset.union_assoc, differenceT]
      rw [FreeMap.FRan_union_add_one (by grind), ih]

      ext t

      simp_all only [RealizeDomSet, exists_and_right, adom.complete_def, Set.mem_diff,
        exists_prop, Set.mem_setOf_eq, not_and, forall_exists_index, projectionT, not_exists, not_forall,
        and_imp, not_true_eq_false, imp_false, forall_true_left, forall_and_index, BoundedFormula.realize_all,
        Nat.succ_eq_add_one]

      apply Iff.intro
      · intro a
        simp_all only [Finset.coe_union, Finset.mem_union, not_or, exists_true_left, and_true]
        intro a_1
        obtain ⟨left, right⟩ := a
        obtain ⟨⟨rn, hrn, t', ht'⟩, left, right_1⟩ := left

        rw [← Finset.coe_union] at left

        let t'' := λ a => ite (a ∈ q.freeVarFinset ∪ FRan (FreeMap n brs)) (t a) (ite (a = FreeMap (n + 1) brs (Fin.last n)) (a_1) (Part.none))

        by_contra hc

        have ⟨rn'', hrn'', t_, ht_⟩ : ∃ rn ∈ adomRs dbi.schema, ∃ t', t' ∈ (dbi.relations rn).tuples := by
          apply adom.exists_tuple_from_value hμ

        have := right t'' rn'' hrn'' t_ ht_ ?_ ?_ ?_
        . rw [← not_forall_not] at this
          apply this
          simp [t'']
          intro x
          apply And.intro
          . intro h₁ h₂ h₃
            cases h₁
            . simp_all
            . simp_all
          . intro h₁ h₂
            rw [@Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, left]
            simp [h₁, h₂]
        . ext x
          simp [t'']
          split
          next h_2 =>
            cases h_2 with
            | inl h_3 => simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
            | inr h_4 =>
              simp_all [Part.dom_iff_mem, ← PFun.mem_dom]
              exact Or.inr (by apply FreeMap.FRan_sub_add_one (by grind) h_4)
          next h_2 =>
            split
            next h_3 =>
              subst h_3
              simp_all only [Part.some_dom, false_or, FRan.mem_def, or_true]
            next h_3 =>
              simp_all [not_or, Part.not_none_dom]
              by_contra hc'
              rw [FreeMap.mem_FRan_add_one_cases (by grind)] at hc'
              simp_all
        . simp [PFun.ran, t'', Set.subset_def]
          intro v a hv
          split at hv
          . apply right_1
            simp [PFun.ran]
            use a
          . split at hv
            . simp [hμ]
            . simp at hv

        . by_contra hc'
          apply hc
          apply (BoundedFormula.Realize.equiv (fun i ↦ ?_) ?_).mp hc'
          . intro a ha
            refine TupleToFun.tuple_eq_att_ext ?_
            simp [t'']
            intro h _
            exact False.elim (h ha)
          . induction i using Fin.lastCases with
            | cast j =>
              have : FreeMap (n + 1) brs j.castSucc ∈ FRan (FreeMap n brs) := by exact FRan.mem_def
              simp only [Fin.snoc_castSucc, Function.comp_apply]
              simp [TupleToFun, t'']
              congr
              simp [this]
              rw [@FreeMap.add_one_def]
            | last =>
              simp [t'']
              have : FreeMap (n + 1) brs (Fin.last n) ∉ q.freeVarFinset ∪ FRan (FreeMap n brs) := by
                exact Finset.notMem_union.mpr (And.intro h (FRan.notMem_FreeMap_lift (by grind)))

              simp [this]

      · intro ⟨⟨w_1, h_1⟩, right⟩
        simp_all only [and_self, and_true]

        apply And.intro
        . exact adom.exists_tuple_from_value hμ
        . intro x rn hrn t' ht' hp hq a

          by_contra hc
          simp at hc

          apply a

          apply (BoundedFormula.Realize.equiv (fun i ↦ ?_) ?_).mp (h_1 ((TupleToFun hp) (FreeMap (n + 1) brs (Fin.last n))))
          . intro a ha
            exact TupleToFun.tuple_eq_att_ext ((hc a).1 (Or.inl ha))
          . induction i using Fin.lastCases with
            | cast j =>
              simp only [Fin.snoc_castSucc, Function.comp_apply]
              simp [TupleToFun]
              have := (hc (FreeMap n brs j)).1 (by simp)
              congr
            | last => simp
