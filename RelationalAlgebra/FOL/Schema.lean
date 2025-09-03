import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

namespace FOL

@[simp]
theorem BoundedFormula.exs.freeVarFinset {k} (φ : fol.BoundedFormula Attribute k) :
  (φ.exs).freeVarFinset = φ.freeVarFinset := by
    induction k
    . simp [BoundedFormula.exs]
    . simp [BoundedFormula.exs]
      simp_all only [BoundedFormula.freeVarFinset, Finset.union_empty]

-- Attributes in query
def BoundedQuery.attributesInQuery {n : ℕ} (q : BoundedQuery n) : Finset Attribute := q.toFormula.freeVarFinset

@[simp]
theorem BoundedQuery.attributesInQuery.R_def [folStruc] {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).attributesInQuery = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    ext x
    simp_all only [attributesInQuery, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset.eq_3, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion, Finset.mem_coe, Set.mem_setOf_eq]

@[simp]
theorem BoundedQuery.attributesInQuery.tEq_def {n : ℕ} (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq t₁ t₂).attributesInQuery = t₁.varFinsetLeft ∪ t₂.varFinsetLeft := by simp_all [attributesInQuery, toFormula]

@[simp]
theorem BoundedQuery.attributesInQuery.and_def {n : ℕ} (q₁ q₂ : BoundedQuery n) :
  (and q₁ q₂).attributesInQuery = q₁.attributesInQuery ∪ q₂.attributesInQuery := by simp_all [attributesInQuery, toFormula]

@[simp]
theorem BoundedQuery.attributesInQuery.ex_def {n : ℕ} (q : BoundedQuery (n + 1)) :
  (ex q).attributesInQuery = q.attributesInQuery := by simp_all [attributesInQuery, toFormula]

@[simp]
theorem BoundedQuery.attributesInQuery.exs_def {n : ℕ} (q : BoundedQuery n) :
  (exs q).attributesInQuery = q.attributesInQuery := by simp [attributesInQuery]


-- schema of query
def BoundedQuery.schema {n : ℕ} : (q : BoundedQuery n) → Finset Attribute
  | .R dbs name vMap => (R dbs name vMap).attributesInQuery
  | .tEq t₁ t₂ => ∅
  | .and q1 q2 => q1.schema ∪ q2.schema
  | .ex q => q.schema

theorem BoundedQuery.schema.sub_attributesInQuery {n} (q : BoundedQuery n) : q.schema ⊆ q.attributesInQuery := by
  induction q
  all_goals simp_all [BoundedQuery.schema, attributesInQuery, BoundedQuery.toFormula, Finset.union_subset_union]

theorem BoundedQuery.schema.sub_attributesInQuery_mem {x n} (q : BoundedQuery n) : x ∈ q.schema → x ∈ q.attributesInQuery :=
  fun a ↦ BoundedQuery.schema.sub_attributesInQuery q a

@[simp]
theorem BoundedQuery.schema.R_def [folStruc] {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).schema = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    simp_all [BoundedQuery.schema]

@[simp]
theorem BoundedQuery.schema.tEq_def {n : ℕ} (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq t₁ t₂).schema = ∅ := by simp_all [BoundedQuery.schema]

@[simp]
theorem BoundedQuery.schema.and_def {n : ℕ} (q₁ q₂ : BoundedQuery n) :
  (and q₁ q₂).schema = q₁.schema ∪ q₂.schema := by simp_all [BoundedQuery.schema]

@[simp]
theorem BoundedQuery.schema.ex_def {n : ℕ} (q : BoundedQuery (n + 1)) :
  (ex q).schema = q.schema := by simp_all [BoundedQuery.schema]

@[simp]
theorem BoundedQuery.schema.exs_def {n : ℕ} (q : BoundedQuery n) :
  (exs q).schema = q.schema := by
    induction n with
    | zero => rfl
    | succ n' ih => exact ih q.ex
