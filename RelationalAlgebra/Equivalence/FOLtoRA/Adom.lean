import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Ordering
import Mathlib.Data.Finset.Union

open RM RA

variable {α ρ μ : Type}

/- Utilities for foldr -/
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


/-- All relations in the database schema that do not have an empty schema-/
def adomRs (dbs : ρ → Finset α) : Set ρ :=
  {rn | dbs rn ≠ ∅}


/-- Empty tuple for a relation -/
def EmptyTupleFromRelation (rn : ρ) : RA.Query ρ α :=
  .p {} (.R rn)

theorem EmptyTupleFromRelation.schema_def [DecidableEq α] : (EmptyTupleFromRelation rn).schema dbs (α := α) = ∅ := rfl

theorem EmptyTupleFromRelation.isWellTyped_def [DecidableEq α] :
  (EmptyTupleFromRelation rn).isWellTyped dbs (α := α) := by simp [EmptyTupleFromRelation]

theorem EmptyTupleFromRelation.evaluateT_def [DecidableEq α] :
  (EmptyTupleFromRelation rn).evaluateT dbi = {t : α →. μ | ∃ x ∈ (dbi.relations rn).tuples, t.Dom = ∅} := by
    simp_rw [EmptyTupleFromRelation, Query.evaluateT, projectionT, Part.eq_none_iff', Set.eq_empty_iff_forall_notMem, Part.dom_iff_mem, ← PFun.mem_dom]
    simp


/-- Empty tuple for multiple relations -/
def EmptyTupleFromRelations (rns : List ρ) (baseRn : ρ) : RA.Query ρ α :=
  rns.foldr (λ rn sq => .u (EmptyTupleFromRelation rn) sq) (.d (EmptyTupleFromRelation baseRn) (EmptyTupleFromRelation baseRn))

theorem EmptyTupleFromRelations.schema_def [DecidableEq α] :
  (EmptyTupleFromRelations rns baseRn).schema dbs (α := α) = ∅ := by
  simp [EmptyTupleFromRelations]
  induction rns with
  | nil => rfl
  | cons hd tl ih => simp_all only [List.foldr_cons, Query.schema.eq_6, EmptyTupleFromRelation.schema_def]

theorem EmptyTupleFromRelations.isWellTyped_def [DecidableEq α] :
  (EmptyTupleFromRelations rns baseRn).isWellTyped dbs (α := α) := by
    simp [EmptyTupleFromRelations]
    induction rns with
    | nil => simp [EmptyTupleFromRelation.isWellTyped_def]
    | cons hd tl ih =>
      rw [List.foldr_cons, Query.isWellTyped, EmptyTupleFromRelation.schema_def, ← EmptyTupleFromRelations]
      rw [← EmptyTupleFromRelations] at ih
      simp [EmptyTupleFromRelation.isWellTyped_def, ih, EmptyTupleFromRelations.schema_def]

theorem EmptyTupleFromRelations.evaluateT_def [DecidableEq α] :
  (EmptyTupleFromRelations rns baseRn).evaluateT dbi = {t : α →. μ | (∃ rn ∈ rns, ∃ x, x ∈ (dbi.relations rn).tuples) ∧ t.Dom = ∅} := by
    simp [EmptyTupleFromRelations]
    induction rns with
    | nil =>
      simp only [List.foldr_nil, Query.evaluateT.eq_7, differenceT,
        EmptyTupleFromRelation.evaluateT_def, exists_and_right]
      ext t
      simp_all
    | cons hd tl ih =>
      rw [List.foldr_cons, Query.evaluateT, ih, unionT, EmptyTupleFromRelation.evaluateT_def]
      ext t
      simp only [exists_and_right, Set.mem_union, Set.mem_setOf_eq, List.mem_cons, exists_eq_or_imp]
      apply Iff.intro
      · intro a
        cases a with
        | inl h => simp_all only [true_or, and_self]
        | inr h_1 => simp_all only [true_and, or_true, and_self]
      · intro a
        simp_all only [and_true]


/-- Tuples with attribute `a` containing all values of `ra` from relation `rn` -/
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
      apply Set.mem_setOf.mpr
      use w
      apply And.intro left
      intro a
      apply And.intro
      . simp [right]
      . intro h
        obtain ⟨right_1, right_2⟩ := right
        simp only [Function.comp_apply, renameFunc]
        split
        next h' =>
          rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, right_2]
          rw [h'] at h
          exact Set.notMem_singleton_iff.mpr fun a ↦ h (id (Eq.symm a))
        next h =>
          rw [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, right_2]
          simp [h]


/--
Tuples with attribute `a` containing all values of all attributes in `ras` from relation `rn`.
Note: `baseRa` should be part of `ras`
-/
def RelationAttributesToColumn [DecidableEq α] (rn : ρ) (ras : List α) (a baseRa : α) : RA.Query ρ α :=
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

section adom_ordering

variable [LinearOrder α] [Inhabited α] {dbs : ρ → Finset α}

/--
Tuples with attribute `a` containing all values from relation `rn`.
Note: the schema of `rn` should not be empty
-/
def RelationNameToColumn (dbs : ρ → Finset α) (rn : ρ) (a : α) : RA.Query ρ α :=
  RelationAttributesToColumn rn (RelationSchema.ordering (dbs rn)) a ((RelationSchema.ordering (dbs rn)).headD default)

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
  {t | (t ∈ ((RelationAttributesToColumn rn (RelationSchema.ordering (dbs rn)) a ((RelationSchema.ordering (dbs rn)).headD default)).evaluateT dbi))} := by
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
          use ((RelationSchema.ordering (dbi.schema rn)).head?.getD default)
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


/--
Tuples with attribute `a` containing all values from any relation in `rns` or `baseRn`.
Note: the schema of all `rns` and `baseRn` should not be empty
-/
def RelationNamesToColumn (dbs : ρ → Finset α) (rns : List ρ) (a : α) (baseRn : ρ) : RA.Query ρ α :=
  rns.foldr (λ rn sq => .u sq (RelationNameToColumn dbs rn a)) (RelationNameToColumn dbs baseRn a)

theorem RelationNamesToColumn.schema_def {a : α}: (RelationNamesToColumn dbs rns a baseRn).schema dbs = ↑{a} := by
  simp [RelationNamesToColumn]
  induction rns with
  | nil => simp [RelationNameToColumn.schema_def]
  | cons hd tl ih => simp_all only [List.foldr_cons, Query.schema.eq_6]

theorem RelationNamesToColumn.isWellTyped_def {a : α} (h : dbs baseRn ≠ ∅) (h' : ∀rn ∈ rns, dbs rn ≠ ∅) :
    (RelationNamesToColumn dbs rns a baseRn).isWellTyped dbs := by
      simp [RelationNamesToColumn]
      induction rns with
      | nil => simp only [List.foldr_nil, RelationNameToColumn.isWellTyped_def h]
      | cons hd tl ih =>
        simp_all only [List.foldr_cons, Query.isWellTyped.eq_6]
        simp_all only [ne_eq, List.mem_cons, or_true, not_false_eq_true, implies_true, forall_const, forall_eq_or_imp,
          true_and]
        obtain ⟨left, right⟩ := h'
        apply And.intro
        · apply RelationNameToColumn.isWellTyped_def left
        · rw [← RelationNamesToColumn]
          rw [schema_def]
          rw [RelationNameToColumn.schema_def]

theorem RelationNamesToColumn.evaluateT_def {a : α} : (RelationNamesToColumn dbs rns a baseRn).evaluateT dbi =
  {t | t ∈ ((RelationNameToColumn dbs baseRn a).evaluateT dbi) ∨ (∃rn ∈ rns, t ∈ ((RelationNameToColumn dbs rn a).evaluateT dbi)) } := by
      simp only [RelationNamesToColumn, Query.foldr_union_evalT]

theorem RelationNamesToColumn.evalT_def {dbi : DatabaseInstance ρ α μ} (h : dbi.schema baseRn ≠ ∅) (h' : ∀rn ∈ rns, dbi.schema rn ≠ ∅) : (RelationNamesToColumn dbi.schema rns a baseRn).evaluateT dbi =
  {t | ∃rn, (rn = baseRn ∨ rn ∈ rns) ∧ t.Dom = {a} ∧ ∃ra ∈ (dbi.schema rn), ∃t' ∈ (dbi.relations rn).tuples, (t' ra = t a)} := by
    ext t
    rw [RelationNamesToColumn.evaluateT_def]
    simp
    apply or_congr
    . rw [RelationNameToColumn.evalT_def h]
      simp
      simp_all only [ne_eq]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h_1⟩ := a_1
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right⟩ := right
        obtain ⟨w_1, h_1⟩ := left_1
        obtain ⟨left_1, right_1⟩ := h_1
        simp_all only [true_and]
        use w_1
        apply And.intro left_1
        use w
      · intro a_1
        simp_all only [and_true]
        obtain ⟨left, right⟩ := a_1
        obtain ⟨w, h_1⟩ := right
        obtain ⟨left, right⟩ := h_1
        obtain ⟨w_2, h_1⟩ := right
        obtain ⟨left_1, right⟩ := h_1
        use w_2
        apply And.intro left_1
        use w
    . apply exists_congr
      intro rn
      apply Iff.intro
      . intro h''
        rw [RelationNameToColumn.evalT_def] at h''
        . simp_all
          obtain ⟨left, right⟩ := h''
          obtain ⟨w, h_1⟩ := right
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          obtain ⟨w_1, h_1⟩ := left_2
          obtain ⟨left_2, right_1⟩ := h_1
          simp_all only [true_and]
          use w_1
          apply And.intro left_2
          use w
        . exact h' rn h''.1
      . intro h''
        rw [RelationNameToColumn.evalT_def]
        . simp_all only [ne_eq, Set.mem_setOf_eq, and_true, true_and]
          obtain ⟨left, right⟩ := h''
          obtain ⟨left_1, right⟩ := right
          obtain ⟨w, h_1⟩ := right
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨w_2, h_1⟩ := right
          obtain ⟨left_2, right⟩ := h_1
          use w_2
          apply And.intro left_2
          use w
        . exact h' rn h''.1


/--
Tuples with attributes `as`, where each attribute maps to an arbitrary value from any relation in `rns` or `baseRn`.
Note: the schema of all `rns` and `baseRn` should not be empty
-/
def RelationNamesToColumns (dbs : ρ → Finset α) (rns : List ρ) (as : List α) (baseRn : ρ) : RA.Query ρ α :=
  as.foldr (λ a sq => .j sq (RelationNamesToColumn dbs rns a baseRn)) (EmptyTupleFromRelations rns baseRn)

theorem RelationNamesToColumns.schema_def {as : List α} : (RelationNamesToColumns dbs rns as baseRn).schema dbs = as.toFinset := by
  simp [RelationNamesToColumns]
  induction as with
  | nil => simp [EmptyTupleFromRelations.schema_def]
  | cons hd tl ih => simp_all [RelationNamesToColumn.schema_def]

theorem RelationNamesToColumns.isWellTyped_def {as : List α} (h : dbs baseRn ≠ ∅) (h' : ∀rn ∈ rns, dbs rn ≠ ∅) :
  (RelationNamesToColumns dbs rns as baseRn).isWellTyped dbs := by
    simp [RelationNamesToColumns]
    induction as with
    | nil => simp [List.foldr_nil, EmptyTupleFromRelations.isWellTyped_def]
    | cons hd tl ih =>
      simp_all only [List.foldr_cons, Query.isWellTyped.eq_4, true_and, RelationNamesToColumn.isWellTyped_def h h']

theorem RelationNamesToColumns.evaluateT_def {dbi : DatabaseInstance ρ α μ} {as : List α} :
    (RelationNamesToColumns dbs rns as baseRn).evaluateT dbi =
      (as.foldr (λ a s => joinT s ((RelationNamesToColumn dbs rns a baseRn).evaluateT dbi))) {t | (∃rn ∈ rns, ∃x, x ∈ (dbi.relations rn).tuples) ∧ t.Dom = ∅} := by
        simp only [RelationNamesToColumns]
        induction as with
        | nil => simp [EmptyTupleFromRelations.evaluateT_def]
        | cons hd tl ih => simp_all only [Query.foldr_join_evalT, joinT, RelationNamesToColumn.evaluateT_def, Query.evaluateT, List.foldr_cons, Query.evaluateT.eq_4]

theorem RelationNamesToColumns.evalT_def {dbi : DatabaseInstance ρ α μ} (h : baseRn ∈ rns) (h' : ∀rn ∈ rns, dbi.schema rn ≠ ∅) :
  (RelationNamesToColumns dbi.schema rns as baseRn).evaluateT dbi =
    {t | (∃rn ∈ rns, ∃t', t' ∈ (dbi.relations rn).tuples) ∧ t.Dom = as.toFinset.toSet ∧ ∀a ∈ as, ∃rn ∈ rns, ∃ra ∈ (dbi.schema rn), ∃t' ∈ (dbi.relations rn).tuples, (t' ra = t a)} := by
      simp only [RelationNamesToColumns]
      induction as with
      | nil => simp [EmptyTupleFromRelations.evaluateT_def]
      | cons hd tl ih =>
        rw [List.foldr_cons, Query.evaluateT, ih]
        ext t
        simp
        simp_all only [ne_eq, Query.foldr_join_evalT, joinT, List.coe_toFinset]
        apply Iff.intro
        · intro a
          simp_all only [joinSingleT, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists, and_imp]
          obtain ⟨w, h_1⟩ := a
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left, right_1⟩ := left
          obtain ⟨w_1, h_1⟩ := right
          obtain ⟨w_2, h_2⟩ := left
          obtain ⟨left, right⟩ := right_1
          obtain ⟨left_1, right_1⟩ := h_1
          obtain ⟨left_2, right_2⟩ := h_2
          obtain ⟨w_3, h_1⟩ := right_2
          apply And.intro
          · use w_2
            apply And.intro left_2
            use w_3
          · apply And.intro
            · have := RA.Query.evaluate.validSchema (RelationNamesToColumn dbi.schema rns hd baseRn) (RelationNamesToColumn.isWellTyped_def (h' baseRn h) h') w_1 left_1
              rw [RelationNamesToColumn.schema_def] at this
              ext a
              rw [Set.mem_insert_iff]
              by_cases h1 : a ∈ w.Dom
              . have h1' := h1
                rw [left] at h1'
                simp [h1']
                simp at h1
                obtain ⟨v, hv⟩ := h1
                rw [(right_1 a).1 v hv]
                exact Exists.intro v hv
              . by_cases h2 : a ∈ w_1.Dom
                . have h2' := h2
                  simp [this] at h2'
                  simp [h2']
                  subst h2'
                  simp at h2
                  obtain ⟨v, hv⟩ := h2
                  rw [(right_1 a).2.1 v hv]
                  exact Exists.intro v hv
                . have h1' := h1
                  rw [left] at h1'
                  have h2' := h2
                  simp [this] at h2'
                  simp [h1', h2']
                  simp [PFun.mem_dom] at h1 h2
                  simp only [(right_1 a).2.2 h1 h2, Part.notMem_none, not_false_eq_true, implies_true]
            · apply And.intro
              rw [RelationNamesToColumn.evalT_def (h' baseRn h) h'] at left_1
              . simp at left_1
                cases left_1
                next h1 =>
                  have ⟨ht_dom', ra, hra, t', ht', ht''⟩ := h1
                  use baseRn
                  apply And.intro h
                  use ra
                  apply And.intro hra
                  use t'
                  apply And.intro ht'
                  have ⟨v, hv⟩ : ∃y, y ∈ w_1 hd := by simp [← PFun.mem_dom, ht_dom']
                  rw [ht'', (right_1 hd).2.1 v hv]
                next h1 =>
                  have ⟨rn, hrn, ht_dom', ra, hra, t', ht', ht''⟩ := h1
                  use rn
                  apply And.intro hrn
                  use ra
                  apply And.intro hra
                  use t'
                  apply And.intro ht'
                  have ⟨v, hv⟩ : ∃y, y ∈ w_1 hd := by simp [← PFun.mem_dom, ht_dom']
                  rw [ht'', (right_1 hd).2.1 v hv]
              · intro a a_1
                have ⟨a', ha', t', ht', ht''⟩ := right a a_1
                use a'
                apply And.intro ha'
                use t'
                apply And.intro ht'
                have ⟨v, hv⟩ : ∃y, y ∈ w a := by simp [← PFun.mem_dom, left, a_1]
                rw [(right_1 a).1 v hv]
                exact ht''
        · intro ⟨⟨rn, hrn, t', ht'⟩, tDom, ⟨rn', hrn', ra, hra, t'', ht'', ht'''⟩, h''⟩
          have dom_tl : ↑tl.toFinset ⊆ t.Dom := by simp [tDom]
          use t.restrict dom_tl
          apply And.intro
          . apply And.intro
            . use rn, hrn, t'
            . apply And.intro
              . ext a
                simp_all only [PFun.mem_dom, List.coe_toFinset, PFun.mem_restrict, Set.mem_setOf_eq, exists_and_left,
                  and_iff_left_iff_imp]
                intro a_1
                simp_all only [List.coe_toFinset, Set.subset_insert]
                have ⟨rn, hrn, ra, hra, t', ht', ht''⟩ := h'' a a_1
                rw [← Part.dom_iff_mem, ← ht'', Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema t' ht', dbi.validSchema]
                exact hra
              · intro a a_1
                have ⟨rn, hrn, ra, hra, t', ht', ht''⟩ := h'' a a_1
                use rn
                apply And.intro hrn
                use ra
                simp_all only [true_and]
                use t'
                simp_all only [List.coe_toFinset, true_and]
                ext a_2 : 1
                simp_all only [PFun.mem_restrict, Set.mem_setOf_eq, true_and]
          . have dom_hd : ↑{hd} ⊆ t.Dom := by simp [tDom]
            use t.restrict dom_hd
            apply And.intro
            . rw [RelationNamesToColumn.evalT_def (h' baseRn h) h']
              . simp_all only [List.coe_toFinset, Set.subset_insert, Set.mem_setOf_eq]
                use rn'
                apply And.intro (Or.inr hrn')
                apply And.intro
                . ext a
                  simp [PFun.dom_eq]
                  intro ha
                  subst ha
                  simp [← PFun.mem_dom]
                  exact dom_hd rfl
                . use ra
                  apply And.intro hra
                  use t''
                  apply And.intro ht''
                  ext v
                  simp only [PFun.mem_restrict, Set.mem_singleton_iff, true_and, ht''']
            . intro a
              apply And.intro
              · intro x h_2
                simp_all only [Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_setOf_eq, true_or,
                  List.coe_toFinset, PFun.mem_restrict]
                obtain ⟨left_2, right_3⟩ := h_2
                ext a_1 : 1
                simp_all only [PFun.mem_restrict, Set.mem_setOf_eq, true_and]
              · apply And.intro
                · intro x h_2
                  simp_all only [List.coe_toFinset, Set.subset_insert, PFun.mem_restrict, Set.mem_singleton_iff]
                  obtain ⟨left_2, right_3⟩ := h_2
                  subst left_2
                  ext a_1 : 1
                  simp_all only [PFun.mem_restrict, Set.mem_singleton_iff, true_and]
                · intro a_1 a_2
                  simp_rw [Set.ext_iff, PFun.mem_dom, ← Part.dom_iff_mem] at tDom
                  simp_rw [PFun.mem_restrict] at a_1 a_2
                  rw [Part.eq_none_iff', tDom a]
                  rw [Not, Set.mem_insert_iff, Set.mem_setOf_eq, ← Not, not_or]
                  apply And.intro
                  . simp only [Set.subset_def, PFun.mem_dom, Set.mem_singleton_iff, forall_eq, not_and] at a_2 dom_hd
                    by_contra hc
                    have ⟨v, hv⟩ := dom_hd
                    subst hc
                    exact a_2 v rfl hv
                  . simp only [Set.subset_def, PFun.mem_dom, List.coe_toFinset, Set.mem_setOf_eq, not_and] at a_1 dom_tl
                    by_contra hc
                    have ⟨v, hv⟩ := dom_tl a hc
                    exact a_1 v hc hv


variable [Inhabited ρ] (dbs : ρ → Finset α) [Fintype (adomRs dbs)] [LinearOrder ρ]

@[simp]
def getRs : List ρ := (adomRs dbs).toFinset.sort (.≤.)

/--
Tuples with attributes `rs`, where each attribute maps to an arbitrary value in the database.
-/
def adom (rs : Finset α) : RA.Query ρ α :=
  RelationNamesToColumns dbs (getRs dbs) (RelationSchema.ordering rs) ((getRs dbs).headD default)

theorem adom.schema_def : (adom dbs rs).schema dbs = rs := by
  simp [adom, RelationNamesToColumns.schema_def]

theorem adom.isWellTyped_def [ne : Nonempty (adomRs dbs)] :
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
          have : x ∈ (adomRs dbs).toFinset.sort (.≤.) := by simp_all
          have : x ∈ (adomRs dbs) := by simp at this; exact this
          rw [adomRs] at this
          simp_all
        next opt heq =>
          simp_all [List.head?_eq_none_iff];
          rw [List.ext_get_iff] at heq
          simp_all only [Finset.length_sort, Set.toFinset_card, List.length_nil, nonempty_subtype,
            Fintype.card_ne_zero, Nat.not_lt_zero, List.get_eq_getElem, IsEmpty.forall_iff,
            implies_true, and_true]
      . intro rn a
        simp_all only [ne_eq]
        simp_all [adomRs]

theorem adom.evaluateT_def {dbi : DatabaseInstance ρ α μ} {as : Finset α} [Fintype (adomRs dbi.schema)] : (adom dbi.schema as).evaluateT dbi =
  {t | t ∈ (RelationNamesToColumns dbi.schema (getRs dbi.schema) (RelationSchema.ordering as) ((getRs dbi.schema).headD default)).evaluateT dbi} := by
    simp [adom]


@[simp]
theorem adom.complete_def {dbi : DatabaseInstance ρ α μ} [Fintype (adomRs dbi.schema)] [Nonempty (adomRs dbi.schema)] :
  (adom dbi.schema as).evaluateT dbi = {t | (∃rn ∈ adomRs dbi.schema, ∃t', t' ∈ (dbi.relations rn).tuples) ∧ t.Dom = ↑as ∧ t.ran ⊆ dbi.domain} := by
    rw [adom, RelationNamesToColumns.evalT_def]
    . rw [DatabaseInstance.domain]
      ext t
      simp_all only [Finset.mem_sort, getRs,
        Set.mem_toFinset, RelationSchema.ordering_eq_toFinset,
        RelationSchema.ordering_mem, Set.mem_setOf_eq, PFun.ran, Set.mem_image,
        Set.setOf_subset_setOf, forall_exists_index]
      apply Iff.intro
      · intro a
        simp_all only [true_and]
        intro a_1 x h
        obtain ⟨left, right⟩ := a
        obtain ⟨w_1, h_2⟩ := left
        obtain ⟨left, right⟩ := right
        obtain ⟨left_1, right_1⟩ := h_2
        obtain ⟨w_2, h_2⟩ := right_1

        have : x ∈ as := by rw [← Finset.mem_coe, ← left, PFun.mem_dom]; use a_1
        obtain ⟨rn, hrn, ra, hra, t', ht', ht''⟩ := right x this
        use rn, ra, t'
        apply And.intro ht'
        rw [ht'']
        exact Part.eq_some_iff.mpr h

      · intro a
        simp_all only [true_and]
        obtain ⟨_, left, right⟩ := a
        intro a ha
        have ⟨v, hv⟩ : ∃v, v ∈ t a := by rw [← PFun.mem_dom, left, Finset.mem_coe]; exact ha
        have ⟨rn, ra, t', ht', ht''⟩ := right v a hv
        use rn
        apply And.intro
        . rw [adomRs, Set.mem_setOf_eq, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_def]
          use ra
          rw [← dbi.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema t' ht', PFun.mem_dom, ht'', ← Part.dom_iff_mem]
          trivial
        . use ra
          apply And.intro
          . rw [← dbi.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema t' ht', PFun.mem_dom, ht'', ← Part.dom_iff_mem]
            trivial
          . use t'
            apply And.intro ht'
            simp_all [← Part.eq_some_iff]

    . simp_all [Option.getD]
      split
      next opt rn' heq =>
        simp_all [List.head?_eq_some_iff]
        obtain ⟨w_1, h_1⟩ := heq
        have : rn' ∈ getRs dbi.schema := by simp_all
        rw [← Set.mem_toFinset]
        exact (Finset.mem_sort fun x1 x2 ↦ x1 ≤ x2).mp this
      next opt heq =>
          simp_all [List.head?_eq_none_iff];
          rw [List.ext_get_iff] at heq
          simp_all only [Finset.length_sort, Set.toFinset_card, List.length_nil, nonempty_subtype,
            Fintype.card_ne_zero, Nat.not_lt_zero, List.get_eq_getElem, IsEmpty.forall_iff,
            implies_true, and_true]
    . simp_all [adomRs]

end adom_ordering


/-- Helper theorems for the adom definition-/
theorem adom.exists_tuple_from_ran {dbi : DatabaseInstance ρ α μ} {t : α →. μ}
  (h : t.Dom ≠ ∅) (h' : t.ran ⊆ dbi.domain) : ∃rn ∈ adomRs dbi.schema, ∃t', t' ∈ (dbi.relations rn).tuples := by
    simp_rw [adomRs, Set.mem_setOf_eq, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_def]
    simp_rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def, PFun.mem_dom] at h
    simp_rw [Set.subset_def, DatabaseInstance.domain, PFun.ran, Set.image, Set.mem_setOf_eq] at h'
    obtain ⟨a, v, h⟩ := h
    obtain ⟨rn, a', t', ht₁, ht₂⟩  := h' v (Exists.intro a h)
    use rn
    apply And.intro
    . simp_rw [← dbi.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema t' ht₁]
      use a'
      rw [PFun.mem_dom]
      use v
      exact Part.eq_some_iff.mp ht₂
    . use t'

theorem adom.exists_tuple_from_value {dbi : DatabaseInstance ρ α μ}
  (h : ∀v, v ∈ dbi.domain) [ne : Inhabited μ] : ∃rn ∈ adomRs dbi.schema, ∃t', t' ∈ (dbi.relations rn).tuples := by
    simp_rw [adomRs, Set.mem_setOf_eq, ← Finset.nonempty_iff_ne_empty, Finset.nonempty_def]
    simp_rw [DatabaseInstance.domain, Set.image, Set.mem_setOf_eq] at h
    obtain ⟨rn, a', t', ht₁, ht₂⟩  := h default
    use rn
    apply And.intro
    . simp_rw [← dbi.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema t' ht₁]
      use a'
      rw [PFun.mem_dom]
      use default
      exact Part.eq_some_iff.mp ht₂
    . use t'
