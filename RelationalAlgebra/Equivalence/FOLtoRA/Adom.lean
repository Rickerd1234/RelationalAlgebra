import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Ordering

open RM RA

variable {α ρ μ : Type}

-- Utility for foldr
@[simp]
theorem RA.Query.foldr_join_schema [DecidableEq α] (xs : List β) (qb : β → RA.Query ρ α) (base : RA.Query ρ α) :
  (xs.foldr (λ a q => q.j (qb a)) base).schema dbs = (xs.foldr (λ a s => s ∪ ((qb a).schema dbs))) (base.schema dbs) := by
    induction xs
    . simp
    . simp_all

@[simp]
theorem RA.Query.foldr_join_evalT (xs : List β) (qb : β → RA.Query ρ α) (base : RA.Query ρ α) :
  (xs.foldr (λ a q => q.j (qb a)) base).evaluateT dbi = (xs.foldr (λ a s => joinT s ((qb a).evaluateT dbi))) (base.evaluateT dbi) := by
    induction xs
    . simp
    . simp_all

@[simp]
theorem RA.Query.foldr_union_evalT (xs : List β) (qb : β → RA.Query ρ α) (base : RA.Query ρ α) :
  (xs.foldr (λ a q => q.u (qb a)) base).evaluateT dbi = {t | t ∈ base.evaluateT dbi ∨ ∃x ∈ xs, t ∈ (qb x).evaluateT dbi} := by
    induction xs with
    | nil =>
      simp_all [List.foldr_nil, List.not_mem_nil, false_and]
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, evaluateT.eq_6, unionT, List.mem_cons, exists_eq_or_imp]
      ext x : 1
      simp_all only [Set.mem_union, Set.mem_setOf_eq]
      apply Iff.intro
      · intro a
        cases a with
        | inl h =>
          cases h with
          | inl h_1 => simp_all only [true_or]
          | inr h_2 => simp_all only [or_true]
        | inr h_1 => simp_all only [true_or, or_true]
      · intro a
        cases a with
        | inl h => simp_all only [true_or]
        | inr h_1 =>
          cases h_1 with
          | inl h => simp_all only [or_true]
          | inr h_2 => simp_all only [or_true, true_or]


-- Database instance value domain
def adomRs (dbs : ρ → Finset α) : Set ρ :=
  {rn | dbs rn ≠ ∅}

def adomAtts (dbs : ρ → Finset α) : Set α :=
  {a | ∃rn, a ∈ dbs rn}


def EmptyTupleFromRelation (rn : ρ) : RA.Query ρ α :=
  .p {} (.R rn)

theorem EmptyTupleFromRelation.schema_def [DecidableEq α] : (EmptyTupleFromRelation rn).schema dbs (α := α) = ∅ := rfl

theorem EmptyTupleFromRelation.isWellTyped_def [DecidableEq α] :
  (EmptyTupleFromRelation rn).isWellTyped dbs (α := α) := by simp [EmptyTupleFromRelation]

theorem EmptyTupleFromRelation.evaluateT_def [DecidableEq α] :
  (EmptyTupleFromRelation rn).evaluateT dbi = {t : α →. μ | ∃ x ∈ (dbi.relations rn).tuples, t.Dom = ∅} := by
    simp_rw [EmptyTupleFromRelation, Query.evaluateT, projectionT, Part.eq_none_iff', Set.eq_empty_iff_forall_notMem, Part.dom_iff_mem, ← PFun.mem_dom]
    simp


def RelationAttributeToColumn [DecidableEq α] (rn : ρ) (ra a : α) : RA.Query ρ α :=
  .r (renameFunc ra a) (.p {ra} (.R rn))

theorem RelationAttributeToColumn.schema_def [DecidableEq α] {a ra : α}: (RelationAttributeToColumn rn ra a).schema dbs = {a} := by
  simp [RelationAttributeToColumn, renameFunc]

theorem RelationAttributeToColumn.isWellTyped_def [DecidableEq α] {a ra : α} (h : ra ∈ dbs rn) :
  (RelationAttributeToColumn rn ra a).isWellTyped dbs := by
    simp [RelationAttributeToColumn, h, rename_func_bijective]

theorem RelationAttributeToColumn.evaluateT_def [DecidableEq α] {a ra : α} : (RelationAttributeToColumn rn ra a).evaluateT dbi =
  {t | t ∈ (renameT (projectionT (dbi.relations rn).tuples {ra}) (renameFunc ra a))} := by
    simp [RelationAttributeToColumn]

theorem RelationAttributeToColumn.evalT_def [DecidableEq α] {dbi : DatabaseInstance ρ α μ} (h_schema : ra ∈ dbi.schema rn) : (RelationAttributeToColumn rn ra a).evaluateT dbi =
  {t | ∃t' ∈ (dbi.relations rn).tuples, t' ra = t a ∧ t.Dom = {a}} := by
    ext t
    simp [RelationAttributeToColumn]
    simp_all only
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      use w
      apply And.intro left
      apply And.intro
      . simp_all [renameFunc]
      . have w_Dom : w.Dom = dbi.schema rn := by rw [← DatabaseInstance.validSchema,  RelationInstance.dom_eq_schema]; exact left
        rw [← Finset.mem_coe, ← w_Dom] at h_schema
        ext x
        rw [Set.mem_singleton_iff, PFun.mem_dom]
        simp [renameFunc] at right
        by_cases hc : x = a
        . simp_all [← PFun.mem_dom]
        . by_cases hc' : x = ra
          . subst hc'
            have := (right a).2 (fun a_1 ↦ hc (id (Eq.symm a_1)))
            simp_all
          . have := (right x).2 hc'
            simp_all
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      simp_all only [ite_self, ↓reduceIte, renameFunc]
      use w
      apply And.intro left
      intro a
      apply And.intro
      . exact fun h => right.1.symm
      . intro h
        obtain ⟨right_1, right_2⟩ := right
        split
        next h' =>
          rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, right_2]
          rw [h'] at h
          exact Set.notMem_singleton_iff.mpr fun a ↦ h (id (Eq.symm a))
        next h =>
          rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, right_2]
          simp [h]


def RelationAttributesToColumn [DecidableEq α] (rn : ρ) (ras : List α) (a : α) (baseRa : α) : RA.Query ρ α :=
  ras.foldr (λ ra sq => .u sq ((RelationAttributeToColumn rn ra a))) (RelationAttributeToColumn rn baseRa a)

theorem RelationAttributesToColumn.schema_def [DecidableEq α] {a : α} : (RelationAttributesToColumn rn ras a baseRa).schema dbs = {a} := by
  simp [RelationAttributesToColumn]
  induction ras with
  | nil => simp [List.foldr_nil, RelationAttributeToColumn.schema_def]
  | cons hd tl ih => simp_all only [List.foldr_cons, Query.schema.eq_6]

theorem RelationAttributesToColumn.isWellTyped_def [DecidableEq α] {a : α}  (h : baseRa ∈ dbs rn) (h' : ∀ra, ra ∈ ras → ra ∈ (dbs rn)) :
  (RelationAttributesToColumn rn ras a baseRa).isWellTyped dbs := by
    simp [RelationAttributesToColumn]
    induction ras with
    | nil => simp_all [List.foldr_nil, RelationAttributeToColumn.isWellTyped_def]
    | cons hd tl ih =>
      simp_all only [List.mem_cons, List.foldr_cons, Query.isWellTyped.eq_6, Query.isWellTyped]
      apply And.intro
      · apply ih
        intro ra a_1
        simp_all only [or_true, implies_true, forall_const, forall_eq_or_imp]
      · apply And.intro
        · apply RelationAttributeToColumn.isWellTyped_def (by simp_all)
        · rw [← RelationAttributesToColumn];
          simp_all [schema_def, RelationAttributeToColumn.schema_def]


theorem RelationAttributesToColumn.evaluateT_def [DecidableEq α] {a : α}  : (RelationAttributesToColumn rn ras a bRa).evaluateT dbi =
  {t | t ∈ (RelationAttributeToColumn rn bRa a).evaluateT dbi ∨
    (∃ra ∈ ras, t ∈ (RelationAttributeToColumn rn ra a).evaluateT dbi)
  } := by
    simp only [RelationAttributesToColumn, Query.foldr_union_evalT]

theorem RelationAttributesToColumn.evalT_def [DecidableEq α] {a : α} {dbi : DatabaseInstance ρ α μ}
  (h_schema : ∀ra ∈ ras, ra ∈ dbi.schema rn) (h_schema' : bRa ∈ dbi.schema rn) : (RelationAttributesToColumn rn ras a bRa).evaluateT dbi =
    {t | ∃t' ∈ (dbi.relations rn).tuples, (t' bRa = t a ∨ (∃ra ∈ ras, t' ra = t a)) ∧ t.Dom = {a}} := by
      ext t
      simp [RelationAttributesToColumn]
      rw [RelationAttributeToColumn.evalT_def h_schema']
      rw [Set.mem_setOf_eq]
      simp only [or_and_right]
      nth_rewrite 3 [← @bex_def]
      simp only [exists_or]
      apply or_congr
      . apply exists_congr
        simp [and_comm, and_assoc]
      . simp only [exists_prop]
        apply Iff.intro
        . intro ⟨ra, hra, ht⟩
          simp [RelationAttributeToColumn.evalT_def (h_schema ra hra)] at ht
          obtain ⟨t', ht', ht'', ht'''⟩ := ht
          use t'
          apply And.intro ht' (And.intro ?_ ht''')
          . use ra
        . intro ⟨t', ht', ⟨ra, hra, hra'⟩, ht'''⟩
          use ra
          apply And.intro hra
          simp [RelationAttributeToColumn.evalT_def (h_schema ra hra)]
          use t'

variable [DecidableEq α] [LE α] [DecidableRel (α := α) (.≤.)] [IsTrans α (.≤.)] [IsAntisymm α (.≤.)] [IsTotal α (.≤.)] [Nonempty α]

noncomputable def RelationNameToColumn (dbs : ρ → Finset α) (rn : ρ) (a : α) : RA.Query ρ α :=
  RelationAttributesToColumn rn (RelationSchema.ordering (dbs rn)) a ((RelationSchema.ordering (dbs rn)).headD (Classical.arbitrary α))

theorem RelationNameToColumn.schema_def {a : α} :
  (RelationNameToColumn dbs rn a).schema dbs = {a} := by
    simp [RelationNameToColumn]
    exact RelationAttributesToColumn.schema_def

theorem RelationNameToColumn.isWellTyped_def {a : α} (h : dbs rn ≠ ∅) :
  (RelationNameToColumn dbs rn a).isWellTyped dbs := by
    simp [RelationNameToColumn]
    apply RelationAttributesToColumn.isWellTyped_def
    . exact RelationSchema.ordering_head?_self_notEmpty h
    . exact fun ra a ↦ (fun a rs ↦ (RelationSchema.ordering_mem a rs).mp) ra (dbs rn) a

theorem RelationNameToColumn.evaluateT_def : (RelationNameToColumn dbs rn a).evaluateT dbi =
  {t | (t ∈ ((RelationAttributesToColumn rn (RelationSchema.ordering (dbs rn)) a ((RelationSchema.ordering (dbs rn)).headD (Classical.arbitrary α))).evaluateT dbi))} := by
    simp [RelationNameToColumn]

theorem RelationNameToColumn.evalT_def {dbi : DatabaseInstance ρ α μ} (h : dbi.schema rn ≠ ∅) : (RelationNameToColumn dbi.schema rn a).evaluateT dbi =
  {t | ∃t' ∈ (dbi.relations rn).tuples, (∃ra ∈ (dbi.schema rn), t' ra = t a) ∧ t.Dom = {a}} := by
    rw [RelationNameToColumn, RelationAttributesToColumn.evalT_def]
    . ext t
      simp_all only [ne_eq, RelationSchema.ordering_mem, Set.mem_setOf_eq]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h_1⟩ := a_1
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right⟩ := right
        simp_all only [and_true]
        cases left_1 with
        | inl h_1 =>
          use w
          simp_all only [true_and]
          use ((RelationSchema.ordering (dbi.schema rn)).head?.getD (Classical.arbitrary α))
          simp_all
        | inr h_2 =>
          obtain ⟨w_1, h_1⟩ := h_2
          obtain ⟨left_1, right_1⟩ := h_1
          use w
          simp_all only [true_and]
          use w_1
      · intro a_1
        obtain ⟨w, h_1⟩ := a_1
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right⟩ := right
        obtain ⟨w_1, h_1⟩ := left_1
        obtain ⟨left_1, right_1⟩ := h_1
        simp_all only [and_true]
        use w
        simp_all only [true_and]
        apply Or.inr
        use w_1
    . simp_all
    . simp_all


noncomputable def RelationNameToColumns (dbs : ρ → Finset α) (rn : ρ) (as : List α) : RA.Query ρ α :=
  as.foldr (λ a sq => .j sq (RelationNameToColumn dbs rn a)) (EmptyTupleFromRelation rn)

theorem RelationNameToColumns.schema_def {as : List α} : (RelationNameToColumns dbs rn as).schema dbs = as.toFinset := by
  simp [RelationNameToColumns]
  induction as with
  | nil => simp [EmptyTupleFromRelation.schema_def]
  | cons hd tl ih => simp_all [RelationNameToColumn.schema_def]

theorem RelationNameToColumns.isWellTyped_def {as : List α} (h : dbs rn ≠ ∅) :
  (RelationNameToColumns dbs rn as).isWellTyped dbs := by
    simp [RelationNameToColumns]
    induction as with
    | nil => simp [List.foldr_nil, EmptyTupleFromRelation.isWellTyped_def]
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, Query.isWellTyped.eq_4, true_and, RelationNameToColumn.isWellTyped_def h]

theorem RelationNameToColumns.evaluateT_def {as : List α} : (RelationNameToColumns dbs rn as).evaluateT dbi =
  (as.foldr (λ a s => joinT s ((RelationNameToColumn dbs rn a).evaluateT dbi))) {t | ∃x ∈ (dbi.relations rn).tuples, t.Dom = ∅} := by
    simp only [RelationNameToColumns]
    induction as with
    | nil => simp [EmptyTupleFromRelation.evaluateT_def]
    | cons hd tl ih => simp_all only [Query.foldr_join_evalT, joinT, RelationNameToColumn.evaluateT_def,
        List.headD_eq_head?_getD, Set.setOf_mem_eq, Query.evaluateT, List.foldr_cons, Query.evaluateT.eq_4]

theorem RelationNameToColumns.evalT_def {dbi : DatabaseInstance ρ α μ} (h : dbi.schema rn ≠ ∅) : (RelationNameToColumns dbi.schema rn as).evaluateT dbi =
  {t | (∃t', t' ∈ (dbi.relations rn).tuples) ∧ t.Dom = as.toFinset.toSet ∧ t.ran ⊆ {v | ∃t att, t ∈ (dbi.relations rn).tuples ∧ t att = .some v}} := by
    simp only [RelationNameToColumns]
    induction as with
    | nil =>
      simp [EmptyTupleFromRelation.evaluateT_def, PFun.ran]
      ext t
      simp
      intro t' ht' ht_dom v a hv
      simp_rw [Set.ext_iff, PFun.mem_dom, Set.mem_empty_iff_false, iff_false, not_exists] at ht_dom
      simp_all
    | cons hd tl ih =>
      rw [List.foldr_cons, Query.evaluateT, ih]
      ext t
      simp
      simp_all only [ne_eq, Query.foldr_join_evalT, joinT, List.coe_toFinset]
      apply Iff.intro
      · intro a
        obtain ⟨w, h_1⟩ := a
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left, right_1⟩ := left
        obtain ⟨w_1, h_1⟩ := right
        obtain ⟨left, right⟩ := left
        obtain ⟨left_1, right_2⟩ := h_1
        obtain ⟨w_2, h_1⟩ := right_1
        apply And.intro
        · use left
        · have w_1_Dom := RA.Query.evaluate.validSchema (RelationNameToColumn dbi.schema rn hd) (RelationNameToColumn.isWellTyped_def h) w_1 left_1
          rw [RelationNameToColumn.schema_def] at w_1_Dom
          have t_Dom : t.Dom = insert hd {a | a ∈ tl} := by
            ext a
            rw [Set.mem_insert_iff]
            by_cases h1 : a ∈ w.Dom
            . have h1' := h1
              rw [w_2] at h1'
              simp [h1']
              simp at h1
              obtain ⟨v, hv⟩ := h1
              rw [(right_2 a).1 v hv]
              exact Exists.intro v hv
            . by_cases h2 : a ∈ w_1.Dom
              . have h2' := h2
                simp [w_1_Dom] at h2'
                simp [h2']
                subst h2'
                simp at h2
                obtain ⟨v, hv⟩ := h2
                rw [(right_2 a).2.1 v hv]
                exact Exists.intro v hv
              . have h1' := h1
                rw [w_2] at h1'
                have h2' := h2
                simp [w_1_Dom] at h2'
                simp [h1', h2']
                simp [PFun.mem_dom] at h1 h2
                simp only [(right_2 a).2.2 h1 h2, Part.notMem_none, not_false_eq_true, implies_true]

          apply And.intro t_Dom
          · simp only [PFun.ran, Set.setOf_subset_setOf, forall_exists_index]
            intro v a hv
            have : a ∈ insert hd {a | a ∈ tl} := by rw [← t_Dom, PFun.mem_dom]; use v
            cases this with
            | inl heq =>
              have ⟨v', hv'⟩ : ∃v', v' ∈ w_1 a := by rw [← PFun.mem_dom, w_1_Dom, heq]; simp
              subst heq
              simp [RelationNameToColumn.evalT_def h] at left_1
              obtain ⟨t', ht', ⟨ra, hra, ht''⟩, _⟩ := left_1
              use t'
              apply And.intro ht'
              use ra
              rw [ht'', ← (right_2 a).2.1 v' hv']
              exact Part.eq_some_iff.mpr hv
            | inr hin =>
              have ⟨v', hv'⟩ : ∃v', v' ∈ w a := by rw [← PFun.mem_dom, w_2]; simp [hin]
              simp [PFun.ran] at h_1
              rw [(right_2 a).1 v' hv'] at hv
              exact h_1 v a hv

      · intro a
        obtain ⟨⟨t', ht'⟩, t_dom, t_ran⟩ := a
        have dom_tl : ↑tl.toFinset ⊆ t.Dom := by simp [t_dom]
        have dom_hd : ↑{hd} ⊆ t.Dom := by simp [t_dom]

        use t.restrict dom_tl
        apply And.intro
        . apply And.intro ?_ (And.intro ?_ ?_)
          . use t'
          . ext a
            simp
            intro heq
            rw [← PFun.mem_dom]
            apply dom_tl
            simp [heq]
          . simp only [PFun.ran, List.coe_toFinset, PFun.mem_restrict, Set.mem_setOf_eq,
              Set.setOf_subset_setOf, forall_exists_index, and_imp] at t_ran ⊢
            exact λ v a ha hv => t_ran v a hv

        . use t.restrict dom_hd
          simp [RelationNameToColumn.evalT_def h]
          apply And.intro
          . simp [PFun.ran] at t_ran
            have ⟨v, hv⟩ : ∃v, v ∈ t hd := by rw [← PFun.mem_dom]; exact dom_hd rfl
            have ⟨t', ht', ⟨ra, hra⟩⟩ := t_ran v hd hv
            use t'
            apply And.intro ht' (And.intro ?_ ?_)
            . use ra
              apply And.intro
              . rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema t' ht', PFun.mem_dom]
                use v
                exact Part.eq_some_iff.mp hra
              . rw [hra, Eq.symm (b := Part.some v) (a := ?_)]
                rw [Part.eq_some_iff]
                simp only [PFun.mem_restrict, Set.mem_singleton_iff, hv, and_self]
            . ext a
              simp
              intro heq
              subst heq
              use v
          . intro a
            apply And.intro ?_ (And.intro ?_ ?_)
            . intro v ha hv
              simp_all only [joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists,
                and_imp, exists_and_left, Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_setOf_eq, true_or]
              ext a_1 : 1
              simp_all only [PFun.mem_restrict, Set.mem_setOf_eq, true_and]
            . intro v ha hv
              subst ha
              simp_all only [joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists,
                and_imp, exists_and_left, List.coe_toFinset, Set.subset_insert]
              ext a_1 : 1
              simp_all only [PFun.mem_restrict, Set.mem_singleton_iff, true_and]
            . intro h1 h2
              simp_rw [Set.ext_iff, PFun.mem_dom, ← Part.dom_iff_mem] at t_dom
              rw [Part.eq_none_iff', t_dom a]
              rw [Not, Set.mem_insert_iff, Set.mem_setOf_eq, ← Not, not_or]
              apply And.intro
              . simp only [Set.subset_def, Set.mem_singleton_iff, PFun.mem_dom, forall_eq] at dom_hd
                by_contra hc
                have ⟨v, hv⟩ := dom_hd
                subst hc
                exact h2 v rfl hv
              . simp only [List.coe_toFinset, Set.subset_def, Set.mem_setOf_eq, PFun.mem_dom] at dom_tl
                by_contra hc
                have ⟨v, hv⟩ := dom_tl a hc
                exact h1 v hc hv


noncomputable def RelationNamesToColumns (dbs : ρ → Finset α) (rns : List ρ) (as : List α) (baseRn : ρ) : RA.Query ρ α :=
  rns.foldr (λ rn sq => .u sq (RelationNameToColumns dbs rn as)) (RelationNameToColumns dbs baseRn as)

theorem RelationNamesToColumns.schema_def {as : List α}: (RelationNamesToColumns dbs rns as baseRn).schema dbs = as.toFinset := by
  simp [RelationNamesToColumns]
  induction rns with
  | nil => simp [RelationNameToColumns.schema_def]
  | cons hd tl ih => simp_all only [List.foldr_cons, Query.schema.eq_6]

theorem RelationNamesToColumns.isWellTyped_def {as : List α} (h : dbs baseRn ≠ ∅) (h' : ∀rn ∈ rns, dbs rn ≠ ∅) :
    (RelationNamesToColumns dbs rns as baseRn).isWellTyped dbs := by
      simp [RelationNamesToColumns]
      induction rns with
      | nil => simp only [List.foldr_nil, RelationNameToColumns.isWellTyped_def h]
      | cons hd tl ih =>
        simp_all only [List.foldr_cons, Query.isWellTyped.eq_6]
        simp_all only [ne_eq, List.mem_cons, or_true, not_false_eq_true, implies_true, forall_const, forall_eq_or_imp,
          true_and]
        obtain ⟨left, right⟩ := h'
        apply And.intro
        · apply RelationNameToColumns.isWellTyped_def left
        · rw [← RelationNamesToColumns]
          rw [schema_def]
          rw [RelationNameToColumns.schema_def]

theorem RelationNamesToColumns.evaluateT_def {as : List α} : (RelationNamesToColumns dbs rns as baseRn).evaluateT dbi =
  {t | t ∈ ((RelationNameToColumns dbs baseRn as).evaluateT dbi) ∨ (∃rn ∈ rns, t ∈ ((RelationNameToColumns dbs rn as).evaluateT dbi)) } := by
      simp only [RelationNamesToColumns, Query.foldr_union_evalT]

theorem RelationNamesToColumns.evalT_def {dbi : DatabaseInstance ρ α μ} (h : dbi.schema baseRn ≠ ∅) (h' : ∀rn ∈ rns, dbi.schema rn ≠ ∅) : (RelationNamesToColumns dbi.schema rns as baseRn).evaluateT dbi =
  {t | ∃rn, (rn = baseRn ∨ rn ∈ rns) ∧ (∃t', t' ∈ (dbi.relations rn).tuples) ∧ t.Dom = as.toFinset.toSet ∧ t.ran ⊆ {v | ∃t att, t ∈ (dbi.relations rn).tuples ∧ t att = .some v}} := by
    ext t
    rw [RelationNamesToColumns.evaluateT_def]
    simp
    apply or_congr
    . rw [RelationNameToColumns.evalT_def h]
      simp
    . apply exists_congr
      intro rn
      apply Iff.intro
      . intro h''
        rw [RelationNameToColumns.evalT_def] at h''
        . simp_all
        . exact h' rn h''.1
      . intro h''
        rw [RelationNameToColumns.evalT_def]
        . simp_all
        . exact h' rn h''.1

variable [Nonempty ρ]  {dbs : ρ → Finset α}

noncomputable def adom (dbs : ρ → Finset α) (rs : Finset α) [Fintype (adomRs dbs)] : RA.Query ρ α :=
  RelationNamesToColumns dbs (adomRs dbs).toFinset.toList (RelationSchema.ordering rs) ((adomRs dbs).toFinset.toList.headD (Classical.arbitrary ρ))

theorem adom.schema_def [Fintype (adomRs dbs)] : (adom dbs rs).schema dbs = rs := by
  simp [adom, RelationNamesToColumns.schema_def]

theorem adom.isWellTyped_def [Fintype (adomRs dbs)] [ne : Nonempty (adomRs dbs)] :
    (adom dbs rs).isWellTyped dbs := by
      simp [adom]
      refine RelationNamesToColumns.isWellTyped_def ?_ ?_
      . simp at ne
        simp
        simp_all [Option.getD]
        split
        next opt x heq =>
          simp [List.head?_eq_some_iff] at heq
          obtain ⟨w, h_1⟩ := heq
          have : x ∈ (adomRs dbs).toFinset.toList := by simp_all
          have : x ∈ (adomRs dbs) := by simp at this; exact this
          rw [adomRs] at this
          exact this
        next opt heq =>
          simp_all [List.head?_eq_none_iff]
      . intro rn a
        simp_all only [Finset.mem_toList, Set.mem_toFinset, ne_eq]
        exact a

theorem adom.evaluateT_def {as : Finset α} [Fintype (adomRs dbs)] : (adom dbs as).evaluateT dbi =
  {t | t ∈ ((RelationNameToColumns dbs ((adomRs dbs).toFinset.toList.headD (Classical.arbitrary ρ)) (RelationSchema.ordering as)).evaluateT dbi)
    ∨ (∃rn ∈ (adomRs dbs).toFinset.toList, t ∈ ((RelationNameToColumns dbs rn (RelationSchema.ordering as)).evaluateT dbi)) } := by
      rw [adom, ← @RelationNamesToColumns.evaluateT_def]


-- Solve this, for some reason the binding of rn is not working properly; Probably need to rearrange the order of join and union of columns :(
@[simp]
theorem adom.complete_def {dbi : DatabaseInstance ρ α μ} [Fintype (adomRs dbi.schema)] [ne : Nonempty (adomRs dbi.schema)] : (adom dbi.schema as).evaluateT dbi =
  {t | (∃rn ∈ adomRs dbi.schema, ∃t', t' ∈ (dbi.relations rn).tuples) ∧ t.Dom = ↑as ∧ t.ran ⊆ dbi.domain} := by
    rw [adom, RelationNamesToColumns.evalT_def]
    . rw [DatabaseInstance.domain]
      ext t
      simp_all only [nonempty_subtype, List.headD_eq_head?_getD, Finset.mem_toList,
        Set.mem_toFinset, RelationSchema.ordering_eq_toFinset, PFun.ran, exists_and_left,
        Set.setOf_subset_setOf, forall_exists_index, exists_eq_or_imp, Set.mem_setOf_eq,
        Set.mem_image]
      apply Iff.intro
      · intro a
        cases a with
        | inl h_1 =>
          obtain ⟨⟨t', ht'⟩, t'_Dom, ht''⟩ := h_1
          simp_all only [true_and]
          apply And.intro
          . use ((adomRs dbi.schema).toFinset.toList.head?.getD (Classical.arbitrary ρ))
            apply And.intro
            . rw [List.head?_eq_some_head]
              . simp
                rw [← Set.mem_toFinset, ← Finset.mem_toList]
                apply List.head_mem
              . simp_all only [ne_eq, Finset.toList_eq_nil, Set.toFinset_eq_empty]
                exact Set.nonempty_iff_ne_empty.mp ne
            . use t'
          . intro v a ha

            have a_1 : a ∈ as := by rw [← Finset.mem_coe, ← t'_Dom, PFun.mem_dom]; use v
            have ⟨t', ht', ra, hra⟩ := ht'' v a ha
            have ⟨v, hv⟩ : ∃v, v ∈ t' ra := by
              use v
              exact Part.eq_some_iff.mp hra

            use ((adomRs dbi.schema).toFinset.toList.head?.getD (Classical.arbitrary ρ))
            use ra
            use t'

        | inr h_1 =>
          obtain ⟨rn, hrn, ⟨t', ht'⟩, t'_Dom, ht''⟩ := h_1
          simp_all only [true_and]
          apply And.intro
          . use rn
            apply And.intro hrn
            use t'
          . intro v a ha

            have a_1 : a ∈ as := by rw [← Finset.mem_coe, ← t'_Dom, PFun.mem_dom]; use v
            have ⟨t', ht', ra, hra⟩ := ht'' v a ha
            have ⟨v, hv⟩ : ∃v, v ∈ t' ra := by
              use v
              exact Part.eq_some_iff.mp hra

            use rn
            use ra
            use t'

      · intro a
        simp_all only [true_and]
        obtain ⟨left, right⟩ := a
        obtain ⟨rn, hrn, t', ht'⟩ := left

        by_cases h_as : as = ∅
        . apply Or.inr
          subst h_as
          simp_all only [Finset.coe_empty]
          use rn
          apply And.intro ?_ (And.intro ?_ ?_)
          . exact hrn
          . exact Exists.intro t' ht'
          . intro v a hv
            obtain ⟨w, h⟩ := ne
            obtain ⟨left, right⟩ := right
            by_contra hc
            simp [Set.ext_iff] at left
            simp_all
        . apply Or.inr
          sorry

    . simp_all [Option.getD]
      split
      next opt rn' heq =>
        simp_all [List.head?_eq_some_iff]
        obtain ⟨w_1, h_1⟩ := heq
        have : rn' ∈ adomRs dbi.schema := by rw [← Set.mem_toFinset, ← Finset.mem_toList]; simp only [h_1, List.mem_cons, true_or]
        simp_all [adomRs]
      next opt heq => simp_all [Set.ext_iff]
    . simp_all [adomRs]
