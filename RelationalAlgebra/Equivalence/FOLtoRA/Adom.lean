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
def RM.DatabaseInstance.domain (dbi : DatabaseInstance ρ α μ) : Set μ :=
    {v | ∃rn att, Part.some v ∈ (dbi.relations rn).tuples.image (λ tup => tup att)}

def adomRs (dbs : ρ → Finset α) : Set ρ :=
  {rn | dbs rn ≠ ∅}

def adomAtts (dbs : ρ → Finset α) : Set α :=
  {a | ∃rn, a ∈ dbs rn}



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

-- Should not use (Query.empty rn) but ?{λ a => none}?

noncomputable def RelationNameToColumns (dbs : ρ → Finset α) (rn : ρ) (as : List α) : RA.Query ρ α :=
  as.foldr (λ a sq => .j sq (RelationNameToColumn dbs rn a)) (.p ∅ (Query.empty rn))

theorem RelationNameToColumns.schema_def {as : List α} : (RelationNameToColumns dbs rn as).schema dbs = as.toFinset := by
  simp [RelationNameToColumns]
  induction as with
  | nil => simp
  | cons hd tl ih => simp_all [RelationNameToColumn.schema_def]

theorem RelationNameToColumns.isWellTyped_def {as : List α} (h : dbs rn ≠ ∅) :
  (RelationNameToColumns dbs rn as).isWellTyped dbs := by
    simp [RelationNameToColumns]
    induction as with
    | nil => simp [List.foldr_nil]
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, Query.isWellTyped.eq_4, true_and, RelationNameToColumn.isWellTyped_def h]

theorem RelationNameToColumns.evaluateT_def {as : List α} : (RelationNameToColumns dbs rn as).evaluateT dbi =
  (as.foldr (λ a s => joinT s ((RelationNameToColumn dbs rn a).evaluateT dbi))) ∅ := by
    simp only [RelationNameToColumns]
    induction as with
    | nil => simp
    | cons hd tl ih => simp_all only [Query.foldr_join_evalT, joinT, RelationNameToColumn.evaluateT_def,
        List.headD_eq_head?_getD, Set.setOf_mem_eq, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or,
        not_exists, and_imp, Query.evaluateT, projectionT, Query.evaluateT.empty_def, Set.mem_empty_iff_false,
        Finset.notMem_empty, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and, false_and, exists_const,
        Set.setOf_false, List.foldr_cons, Query.evaluateT.eq_4]

theorem RelationNameToColumns.evalT_def {dbi : DatabaseInstance ρ α μ} (h : dbi.schema rn ≠ ∅) : (RelationNameToColumns dbi.schema rn as).evaluateT dbi =
  {t | t.Dom = as.toFinset.toSet ∧ ∃a ∈ as, ∃ra ∈ (dbi.schema rn), ∃t' ∈ (dbi.relations rn).tuples, (t' ra = t a)} := by
    sorry

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
  {t | ∃rn, (rn = baseRn ∨ rn ∈ rns) ∧ t.Dom = as.toFinset.toSet ∧ ∃a ∈ as, ∃ra ∈ (dbi.schema rn), ∃t' ∈ (dbi.relations rn).tuples, (t' ra = t a)} := by
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

-- Explore possibilities of t.Dom = as ∧ t.ran = dbi.domain

@[simp]
theorem adom.complete_def {dbi : DatabaseInstance ρ α μ} [Fintype (adomRs dbi.schema)] [ne : Nonempty (adomRs dbi.schema)] : (adom dbi.schema as).evaluateT dbi =
  {t | t.Dom = ↑as ∧ ∃a ∈ as, ∃v ∈ dbi.domain, t a = .some v} := by
    rw [adom, RelationNamesToColumns.evalT_def]
    . rw [DatabaseInstance.domain]
      ext t
      simp_all only [nonempty_subtype, List.headD_eq_head?_getD, Finset.mem_toList, Set.mem_toFinset,
        RelationSchema.ordering_eq_toFinset, RelationSchema.ordering_mem, exists_eq_or_imp, Set.mem_setOf_eq,
        Set.mem_image]
      obtain ⟨w, h⟩ := ne
      apply Iff.intro
      · intro a
        cases a with
        | inl h_1 =>
          obtain ⟨left, right⟩ := h_1
          obtain ⟨w_1, h_1⟩ := right
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨w_2, h_1⟩ := right
          obtain ⟨left_2, right⟩ := h_1
          obtain ⟨w_3, h_1⟩ := right
          obtain ⟨left_3, right⟩ := h_1
          apply And.intro left
          use w_1
          apply And.intro left_1
          have : (t w_1).Dom := by
            rw [← right, Part.dom_iff_mem, ← PFun.mem_dom]
            rw [(dbi.relations _).validSchema w_3 left_3, Finset.mem_coe, DatabaseInstance.validSchema]
            exact left_2
          use (t w_1).get this
          simp_all only [Part.some_get, and_true]
          apply Exists.intro
          · apply Exists.intro
            · apply Exists.intro
              · apply And.intro
                · exact left_3
                · exact right
        | inr h_2 =>
          obtain ⟨w_1, h_1⟩ := h_2
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left_1, right⟩ := right
          obtain ⟨w_2, h_1⟩ := right
          obtain ⟨left_2, right⟩ := h_1
          obtain ⟨w_3, h_1⟩ := right
          obtain ⟨left_3, right⟩ := h_1
          obtain ⟨w_4, h_1⟩ := right
          obtain ⟨left_4, right⟩ := h_1
          apply And.intro left_1
          use w_2
          apply And.intro left_2
          have : (t w_2).Dom := by
            rw [← right, Part.dom_iff_mem, ← PFun.mem_dom]
            rw [(dbi.relations w_1).validSchema w_4 left_4, Finset.mem_coe, DatabaseInstance.validSchema]
            exact left_3
          use (t w_2).get this
          simp_all only [Part.some_get, and_true]
          apply Exists.intro
          · apply Exists.intro
            · apply Exists.intro
              · apply And.intro
                · exact left_4
                · exact right
      · intro a
        simp_all only [true_and]
        obtain ⟨left, right⟩ := a
        obtain ⟨a, h_1⟩ := right
        obtain ⟨left_1, right⟩ := h_1
        obtain ⟨v, h_1⟩ := right
        obtain ⟨left_2, right⟩ := h_1
        obtain ⟨rn', h_1⟩ := left_2
        obtain ⟨ra, h_1⟩ := h_1
        obtain ⟨t', h_1⟩ := h_1
        obtain ⟨ht', ht'_eq⟩ := h_1
        apply Or.inr
        use rn'
        have : ra ∈ dbi.schema rn' := by
          have := (dbi.relations rn').validSchema t' ht'
          simp only [Set.ext_iff, PFun.mem_dom, DatabaseInstance.validSchema, Finset.mem_coe] at this
          exact (this ra).mp (Exists.intro v (Part.eq_some_iff.mp ht'_eq))
        apply And.intro
        . rw [adomRs, Set.mem_setOf_eq]
          by_contra hc
          rw [hc] at this
          exact (Finset.notMem_empty ra) this
        . use a
          simp [left_1]
          use ra
          apply And.intro this
          . use t'
            simp_all

    . simp_all [Option.getD]
      split
      next opt rn' heq =>
        simp_all [List.head?_eq_some_iff]
        obtain ⟨w_1, h_1⟩ := heq
        have : rn' ∈ adomRs dbi.schema := by rw [← Set.mem_toFinset, ← Finset.mem_toList]; simp only [h_1, List.mem_cons, true_or]
        simp_all [adomRs]
      next opt heq => simp_all [Set.ext_iff]
    . simp_all [adomRs]
