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
theorem BoundedQuery.attributesInQuery.R_def_mem [folStruc] {n : ℕ} {x : Attribute} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  x ∈ (R dbs rn t).attributesInQuery ↔ ∃i : Fin (dbs rn).card, x ∈ (t i).varFinsetLeft := by
    simp_all only [attributesInQuery, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

instance BoundedQuery.attributesInQuery.R_fintype [folStruc] {rn} {dbs : DatabaseSchema} {t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  Fintype {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    apply Fintype.ofFinset ((BoundedQuery.R dbs rn t).attributesInQuery)
    simp_all [BoundedQuery.attributesInQuery.R_def_mem]

@[simp]
theorem BoundedQuery.attributesInQuery.R_def [folStruc] {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).attributesInQuery = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft}.toFinset := by
    exact Eq.symm (Set.toFinset_ofFinset (R dbs rn t).attributesInQuery R_fintype._proof_2)

@[simp]
theorem BoundedQuery.attributesInQuery.tEq_def {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq q t₁ t₂).attributesInQuery = q.attributesInQuery ∪ t₁.varFinsetLeft ∪ t₂.varFinsetLeft := by simp_all [attributesInQuery, toFormula]

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
  | .tEq q _ _ => q.schema
  | .and q1 q2 => q1.schema ∪ q2.schema
  | .ex q => q.schema

theorem BoundedQuery.schema.sub_attributesInQuery {n} (q : BoundedQuery n) : q.schema ⊆ q.attributesInQuery := by
  induction q
  all_goals simp_all [BoundedQuery.schema, attributesInQuery, BoundedQuery.toFormula, Finset.union_subset_union]
  . rw [Finset.subset_iff]; aesop

theorem BoundedQuery.schema.sub_attributesInQuery_mem {x n} (q : BoundedQuery n) : x ∈ q.schema → x ∈ q.attributesInQuery :=
  fun a ↦ BoundedQuery.schema.sub_attributesInQuery q a

@[simp]
theorem BoundedQuery.schema.R_def [folStruc] {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).schema = (R dbs rn t).attributesInQuery := by rfl

@[simp]
theorem BoundedQuery.schema.tEq_def {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq q t₁ t₂).schema = q.schema := by simp_all [BoundedQuery.schema]

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
