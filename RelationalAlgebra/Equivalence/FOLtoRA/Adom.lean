import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Ordering

open RM RA

def adomRs (dbs : DatabaseSchema) : Set RelationName :=
  {rn | dbs rn ≠ ∅}

def adomAtts (dbs : DatabaseSchema) : Set Attribute :=
  {a | ∃rn, a ∈ dbs rn}

def renameColumn (rn : RelationName) (a a' : Attribute) : RA.Query :=
  (.p {a} (.r (renameFunc a a') (.R rn)))

@[simp]
theorem renameColumn.schema_def : (renameColumn rn a a').schema dbs = {a} := by
  simp [renameColumn]

@[simp]
theorem renameColumn.isWellTyped_def (h'' : a' ∈ dbs rn) : (renameColumn rn a a').isWellTyped dbs := by
  simp [renameColumn]
  apply And.intro
  . exact rename_func_bijective a a'
  . use a'
    simp_all [renameFunc]

theorem renameColumn.evaluateT_def : (renameColumn rn a a').evaluateT dbi =
  projectionT (renameT (dbi.relations rn).tuples (renameFunc a a')) {a} := by
    simp [renameColumn]

def getColumn (rn : RelationName) (a : Attribute) (as : List Attribute) : RA.Query :=
  as.foldr (λ a' q => q.u (renameColumn rn a a')) (.d (.p {a} (.R rn)) (.p {a} (.R rn)))

@[simp]
theorem getColumn.schema_def : (getColumn rn a as).schema dbs = {a} := by
  induction as with
  | nil => simp [getColumn]
  | cons hd tl ih => simp_all [getColumn]

@[simp]
theorem getColumn.isWellTyped_def (h : a ∈ dbs rn) (h'' : ∀a', a' ∈ as → a' ∈ dbs rn) : (getColumn rn a as).isWellTyped dbs := by
  induction as with
  | nil => simp [getColumn, h]
  | cons hd tl ih =>
    simp_all [getColumn, ih]
    exact schema_def

theorem getColumn.evaluateT_def : (getColumn rn a as).evaluateT dbi =
  {t | ∃a' ∈ as, t ∈ (renameColumn rn a a').evaluateT dbi} := by
    induction as with
    | nil =>
      simp [getColumn, diffT, Set.ext_iff, Set.diff]
    | cons hd tl ih =>
      simp [getColumn, unionT]
      rw [← getColumn, ih]
      aesop

def joinColumns (rn : RelationName) (as as' : List Attribute) : RA.Query :=
  as.foldr (λ a q => q.j (getColumn rn a as')) (.d (.p {} (.R rn)) (.p {} (.R rn)))

@[simp]
theorem joinColumns.schema_def : (joinColumns rn as as').schema dbs = as.toFinset := by
  induction as with
  | nil => simp [joinColumns]
  | cons hd tl ih => simp_all [joinColumns]; aesop

@[simp]
theorem joinColumns.isWellTyped_def {as as' : List Attribute} (h : ∀a', a' ∈ as → a' ∈ dbs rn) (h' : ∀a', a' ∈ as' → a' ∈ dbs rn) : (joinColumns rn as as').isWellTyped dbs := by
  induction as with
  | nil => simp [joinColumns]
  | cons hd tl ih =>
    simp [joinColumns]
    simp_all
    exact ih

set_option maxHeartbeats 2000000

theorem joinColumns.evaluateT_def : (joinColumns rn as as').evaluateT dbi =
  {t | ∀a ∈ as, ∃ t2 ∈ (getColumn rn a as').evaluateT dbi,
        (∀ x_1 ∈ t2 a, t a = t2 a) ∧ ((∀ (x : Value), x ∉ t a) → (∀ (x : Value), x ∉ t2 a) → t a = Part.none)} := by
    induction as with
    | nil =>
      simp [joinColumns, diffT]
    | cons hd tl ih =>
      simp [joinColumns, joinT, Set.ext_iff, Set.diff]
      rw [← joinColumns, ih]
      intro t
      simp_all only [List.empty_eq, ne_eq, Set.mem_setOf_eq]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        -- obtain ⟨left, right_1⟩ := left
        obtain ⟨w_1, h⟩ := right
        obtain ⟨left_1, right⟩ := h
        -- simp_all only [not_false_eq_true, true_and]
        apply And.intro
        · use w_1
          simp_all only [true_and]
          apply And.intro
          · intro x_1 a
            exact (right hd).2.1 x_1 a
          · intro a a_1
            exact Part.eq_none_iff.mpr a
        · intro a a_1
          have ⟨w, hw⟩ := left a a_1
          use w
          simp_all only [true_and]
          obtain ⟨left_2, right_2⟩ := hw
          obtain ⟨left_3, right_2⟩ := right_2
          apply And.intro
          · intro x_1 a_2
            rw [← left_3 x_1 a_2] at *
            exact (right a).1 x_1 a_2
          · intro a_2 a_3
            simp_all only [not_isEmpty_of_nonempty, IsEmpty.forall_iff, not_true_eq_false, implies_true,
              not_false_eq_true, forall_const]
            exact Part.eq_none_iff.mpr a_2
      · intro a
        obtain ⟨left, right⟩ := a
        obtain ⟨w, h⟩ := left
        obtain ⟨left, right_1⟩ := h
        obtain ⟨left_1, right_1⟩ := right_1
        use w
        apply And.intro
        · intro a a_1
          have ⟨w, hw⟩ := right a a_1
          use w
          simp_all only [true_and]
          obtain ⟨left_2, right_2⟩ := hw
          obtain ⟨left_3, right_2⟩ := right_2
          apply And.intro
          · intro x_1 a_2
            rw [← left_3 x_1 a_2] at *
            sorry
          · intro a_2 a_3
            simp_all only [not_isEmpty_of_nonempty, IsEmpty.forall_iff, not_true_eq_false, implies_true,
              not_false_eq_true, forall_const]
            exact Part.eq_none_iff.mpr a_2
        · use t
          simp_all only [not_false_eq_true, implies_true, forall_const, and_self_left, true_and]
          aesop
          convert left
          sorry

def unionRels (rns : List RelationName) (as : List Attribute) : RA.Query :=
  rns.foldr (λ rn q => q.u (joinColumns rn as as)) (.d (.p as.toFinset (.R default)) (.p as.toFinset (.R default)))

theorem unionRels_def (rns) (as) : unionRels rns as = rns.foldr (λ rn q => q.u (joinColumns rn as as)) (.d (.p as.toFinset (.R default)) (.p as.toFinset (.R default))) := rfl

@[simp]
theorem unionRels.schema_def : (unionRels rns as).schema dbs = as.toFinset := by
  induction rns with
  | nil => simp [unionRels]
  | cons hd tl ih => simp_all [unionRels]

@[simp]
theorem unionRels.isWellTyped_def {as : List Attribute} (h : ∀rn, ∀a', a' ∈ as → a' ∈ dbs rn) : (unionRels rns as).isWellTyped dbs := by
  induction rns with
  | nil => simp [unionRels, Finset.subset_iff]; exact h ""
  | cons hd tl ih =>
    simp [unionRels, ih]
    apply And.intro
    · exact ih
    · apply And.intro
      . exact joinColumns.isWellTyped_def (h hd) (h hd)
      . rw [← String.default_eq, ← unionRels_def tl as]
        exact schema_def

theorem unionRels.evaluateT_def : (unionRels rns as).evaluateT dbi =
  {t | ∃rn ∈ rns, t ∈ (joinColumns rn as as).evaluateT dbi} := by
    induction rns with
    | nil =>
      simp [unionRels, diffT, Set.ext_iff, Set.diff]
    | cons hd tl ih =>
      simp [unionRels, unionT]
      rw [← String.default_eq, ← unionRels, ih]
      aesop

variable (dbi : DatabaseInstance) [h : Fintype ↑(adomRs (dbi.schema))] [h' : Fintype ↑(adomAtts (dbi.schema))]

def adom : Query :=
  unionRels ((adomRs (dbi.schema)).toFinset.sort (.≤.)) (RelationSchema.ordering (adomAtts (dbi.schema)).toFinset)

@[simp]
theorem adom_schema : ↑((adom dbi).schema dbi.schema) = adomAtts dbi.schema := by
  ext a
  simp [adom, adomAtts]

@[simp]
theorem adom_evaluateT : (adom dbi).evaluateT dbi = {t | ∃rn ∈ adomRs dbi.schema, ∃a ∈ adomAtts dbi.schema, ∃t' ∈ (dbi.relations rn).tuples, t a = t' a} := by
  simp [adomRs, adomAtts, adom]; sorry

theorem adom_all (h : a ∈ adomAtts dbi.schema) (h' : v ∈ dbi.domain): ∃t ∈ (adom dbi).evaluateT dbi, t a = v := by
  simp_all [adomAtts, Query.evaluateT, adom, DatabaseInstance.domain];
