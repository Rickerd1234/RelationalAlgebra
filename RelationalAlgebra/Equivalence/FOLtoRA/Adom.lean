import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Ordering

open RM RA

-- Utility for foldr
@[simp]
theorem RA.Query.foldr_join (xs : List α) (qb : α → RA.Query) (base : RA.Query) :
  (xs.foldr (λ a q => q.j (qb a)) base).evaluateT dbi = (xs.foldr (λ a s => joinT s ((qb a).evaluateT dbi))) (base.evaluateT dbi) := by
    induction xs
    . simp
    . simp_all

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

@[simp]
theorem renameColumn.evaluateT_def : (renameColumn rn a a').evaluateT dbi =
  projectionT (renameT (dbi.relations rn).tuples (renameFunc a a')) {a} := by
    simp [renameColumn]

def getColumn (rn : RelationName) (a : Attribute) (as : List Attribute) : RA.Query :=
  as.foldr (λ a' q => q.u (renameColumn rn a a')) (.p {a} (Query.empty rn))

@[simp]
theorem getColumn.schema_def : (getColumn rn a as).schema dbs = {a} := by
  induction as with
  | nil => simp [getColumn]
  | cons hd tl ih => simp_all [getColumn]

@[simp]
theorem getColumn.isWellTyped_def (h : a ∈ dbs rn) (h'' : ∀a', a' ∈ as → a' ∈ dbs rn) : (getColumn rn a as).isWellTyped dbs := by
  induction as with
  | nil => simp [getColumn, h, Query.empty]
  | cons hd tl ih =>
    simp_all [getColumn, ih]
    exact schema_def

@[simp]
theorem getColumn.evaluateT_def : (getColumn rn a as).evaluateT dbi =
  {t | ∃a' ∈ as, t ∈ (renameColumn rn a a').evaluateT dbi} := by
    induction as with
    | nil =>
      simp [getColumn, projectionT, Query.evaluateT.empty_def]
    | cons hd tl ih =>
      simp [getColumn, unionT]
      rw [← getColumn, ih]
      aesop

def joinColumns (rn : RelationName) (as as' : List Attribute) : RA.Query :=
  as.foldr (λ a q => q.j (getColumn rn a as')) (.p {} (Query.empty rn))

@[simp]
theorem joinColumns.schema_def : (joinColumns rn as as').schema dbs = as.toFinset := by
  induction as with
  | nil => simp [joinColumns]
  | cons hd tl ih => simp_all [joinColumns]; aesop

@[simp]
theorem joinColumns.isWellTyped_def {as as' : List Attribute} (h : ∀a', a' ∈ as → a' ∈ dbs rn) (h' : ∀a', a' ∈ as' → a' ∈ dbs rn) : (joinColumns rn as as').isWellTyped dbs := by
  induction as with
  | nil => simp [joinColumns, Query.empty]
  | cons hd tl ih =>
    simp [joinColumns]
    simp_all
    exact ih

@[simp]
theorem joinColumns.evaluateT_def : (joinColumns rn as as').evaluateT dbi =
  (as.foldr (λ a s => joinT s ((getColumn rn a as').evaluateT dbi))) ((Query.empty rn).evaluateT dbi) := by
    induction as with
    | nil =>
      simp [joinColumns, Query.evaluateT.empty_def, projectionT]
    | cons hd tl ih =>
      simp [joinColumns, Set.ext_iff, Query.evaluateT.empty_def, projectionT]

def unionRels (rns : List RelationName) (as : List Attribute) : RA.Query :=
  rns.foldr (λ rn q => q.u (joinColumns rn as as)) (.p as.toFinset (Query.empty default))

theorem unionRels_def (rns) (as) : unionRels rns as = rns.foldr (λ rn q => q.u (joinColumns rn as as)) (.p as.toFinset (Query.empty default)) := by rfl

@[simp]
theorem unionRels.schema_def : (unionRels rns as).schema dbs = as.toFinset := by
  induction rns with
  | nil => simp [unionRels]
  | cons hd tl ih => simp_all [unionRels]

@[simp]
theorem unionRels.isWellTyped_def {as : List Attribute} (h : ∀rn, ∀a', a' ∈ as → a' ∈ dbs rn) : (unionRels rns as).isWellTyped dbs := by
  induction rns with
  | nil => simp [unionRels, Finset.subset_iff, Query.empty]; exact h ""
  | cons hd tl ih =>
    simp [unionRels, ih]
    apply And.intro
    · exact ih
    · apply And.intro
      . exact joinColumns.isWellTyped_def (h hd) (h hd)
      . rw [← String.default_eq, ← unionRels_def tl as]
        exact schema_def

@[simp]
theorem unionRels.evaluateT_def : (unionRels rns as).evaluateT dbi =
  {t | ∃rn ∈ rns, t ∈ (joinColumns rn as as).evaluateT dbi} := by
    induction rns with
    | nil =>
      simp [unionRels, projectionT, Query.evaluateT.empty_def]
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
theorem adom.evaluateT_def : (adom dbi).evaluateT dbi =
  (unionRels
    ((adomRs (dbi.schema)).toFinset.sort (.≤.))
    (RelationSchema.ordering (adomAtts (dbi.schema)).toFinset)
  ).evaluateT dbi :=
    by rfl

-- main theorem
theorem adom_all (h_attr : a ∈ adomAtts dbi.schema) (h_val : v ∈ dbi.domain) :
  ∃ t ∈ (adom dbi).evaluateT dbi, t a = v := by
    simp_all [DatabaseInstance.domain, adomAtts, adomRs]
    sorry
