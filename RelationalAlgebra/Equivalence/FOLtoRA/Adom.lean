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

-- Database instance value domain
def RM.DatabaseInstance.domain (dbi : DatabaseInstance) : Set Value :=
    {v | ∃rn att, Part.some v ∈ (dbi.relations rn).tuples.image (λ tup => tup att)}

def adomRs (dbs : DatabaseSchema) : Set RelationName :=
  {rn | dbs rn ≠ ∅}

def adomAtts (dbs : DatabaseSchema) : Set Attribute :=
  {a | ∃rn, a ∈ dbs rn}

def renameColumn (rn : RelationName) (a ra : Attribute) : RA.Query :=
  .r (renameFunc a ra) (.p {ra} (.R rn))

@[simp]
theorem renameColumn.schema_def : (renameColumn rn a ra).schema dbs = {a} := by
  simp [renameColumn, renameFunc]

@[simp]
theorem renameColumn.isWellTyped_def (h'' : ra ∈ dbs rn) : (renameColumn rn a ra).isWellTyped dbs := by
  simp [renameColumn]
  apply And.intro
  . exact h''
  . exact rename_func_bijective a ra

-- @[simp]
-- theorem renameColumn.evaluateT_def : (renameColumn rn a ra).evaluateT dbi =
--   (renameT (projectionT (dbi.relations rn).tuples {ra}) (renameFunc a ra)) := by
--     simp [renameColumn]

-- def getColumn (rn : RelationName) (a : Attribute) (ras : List Attribute) : RA.Query :=
--   ras.foldr (λ ra q => q.u (renameColumn rn a ra)) (.p {} (Query.empty rn))

-- @[simp]
-- theorem getColumn.schema_def : (getColumn rn a as).schema dbs = {a} := by
--   induction as with
--   | nil => simp [getColumn]
--   | cons hd tl ih => simp_all [getColumn]

-- @[simp]
-- theorem getColumn.isWellTyped_def (h'' : ∀a', a' ∈ ras → a' ∈ dbs rn) : (getColumn rn a ras).isWellTyped dbs := by
--   induction ras with
--   | nil => simp [getColumn, h, Query.empty]
--   | cons hd tl ih =>
--     simp_all [getColumn, ih]
--     exact schema_def

-- @[simp]
-- theorem getColumn.evaluateT_def : (getColumn rn a as).evaluateT dbi =
--   {t | ∃a' ∈ as, t ∈ (renameColumn rn a a').evaluateT dbi} := by
--     induction as with
--     | nil =>
--       simp [getColumn, projectionT, Query.evaluateT.empty_def]
--     | cons hd tl ih =>
--       simp [getColumn, unionT]
--       rw [← getColumn, ih]
--       aesop

def joinColumns (rn : RelationName) (ra : Attribute) (as : List Attribute) : RA.Query :=
  as.foldr (λ a q => q.j (renameColumn rn a ra)) (.p as.toFinset (Query.empty rn))

@[simp]
theorem joinColumns.schema_def : (joinColumns rn ra as).schema dbs = as.toFinset := by
  induction as with
  | nil => simp [joinColumns]
  | cons hd tl ih => simp_all [joinColumns]; sorry

@[simp]
theorem joinColumns.isWellTyped_def (h'' : ra ∈ dbs rn) : (joinColumns rn ra as).isWellTyped dbs := by
  induction as with
  | nil => simp [joinColumns, Query.empty]
  | cons hd tl ih =>
    rw [joinColumns]
    simp
    aesop?


@[simp]
theorem joinColumns.evaluateT_def : (joinColumns rn as as').evaluateT dbi =
  (as.foldr (λ a s => joinT s ((getColumn rn a as').evaluateT dbi))) ((Query.empty rn).evaluateT dbi) := by
    induction as with
    | nil =>
      simp [joinColumns, Query.evaluateT.empty_def, projectionT]
    | cons hd tl ih =>
      simp [joinColumns, Set.ext_iff, Query.evaluateT.empty_def, projectionT]

def unionRels (rns : List RelationName) (as : List Attribute) : RA.Query :=
  rns.foldr (λ rn q => q.u (joinColumns rn a ra)) (.p as.toFinset (Query.empty default))

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
      ext x : 1
      simp_all only [joinColumns.evaluateT_def, joinT, getColumn.evaluateT_def,
        renameColumn.evaluateT_def, projectionT, renameT, exists_eq_right', Set.mem_setOf_eq,
        Finset.mem_singleton, PFun.mem_dom, forall_exists_index, Set.mem_union, not_or, not_exists,
        and_imp, Query.evaluateT.empty_def]
      apply Iff.intro Or.symm Or.symm

variable (dbs : DatabaseSchema) [hf : Fintype ↑(adomRs dbs)]

def adom (rs : RelationSchema) : Query :=
  unionRels ((adomRs dbs).toFinset.sort (.≤.)) rs.ordering

@[simp]
theorem adom_schema : ↑((adom dbs rs).schema dbs) = rs := by
  ext a
  simp [adom, adomAtts]

@[simp]
theorem adom.isWellTyped_def (h : ↑rs ⊆ adomAtts dbs) : (adom dbs rs).isWellTyped dbs := by
  simp [adom]; exact unionRels.isWellTyped_def (by simp_all [adomAtts]; intro rn a ha; sorry)

@[simp]
theorem adom.evaluateT_def (dbi : DatabaseInstance) : (adom dbs rs).evaluateT dbi =
  (unionRels
    ((adomRs (dbs)).toFinset.sort (.≤.))
    (rs.ordering)
  ).evaluateT dbi :=
    by rfl

-- main theorem
theorem adom_all {dbi : DatabaseInstance} (h_attr : a ∈ rs) (h_val : v ∈ dbi.domain) (h_wt : (adom dbs rs).isWellTyped dbs) :
  ∃ t ∈ (adom dbs rs).evaluateT dbi, t a = v := by
    simp_all [DatabaseInstance.domain, adomAtts, adomRs, adom]
    sorry
