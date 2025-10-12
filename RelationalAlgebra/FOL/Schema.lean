import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

namespace FOL

-- Extend ModelTheory
@[simp]
theorem BoundedFormula.exs.freeVarFinset {k} (φ : fol.BoundedFormula Attribute k) :
  (φ.exs).freeVarFinset = φ.freeVarFinset := by
    induction k
    . simp [BoundedFormula.exs]
    . simp [BoundedFormula.exs]
      simp_all only [BoundedFormula.freeVarFinset, Finset.union_empty]

-- schema of query
def BoundedQuery.schema {n : ℕ} (q : BoundedQuery dbs n) : Finset Attribute :=
  q.toFormula.freeVarFinset

@[simp]
theorem BoundedQuery.schema.R_def_mem {n : ℕ} {x : Attribute} {dbs : DatabaseSchema} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  x ∈ (R rn t).schema ↔ ∃i : Fin (dbs rn).card, x ∈ (t i).varFinsetLeft := by
    simp_all only [schema, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

instance BoundedQuery.schema.R_fintype {rn} {dbs : DatabaseSchema} {t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  Fintype {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    apply Fintype.ofFinset ((BoundedQuery.R rn t).schema)
    simp only [BoundedQuery.schema.R_def_mem, Set.mem_setOf_eq, implies_true]

@[simp]
theorem BoundedQuery.schema.R_def {n : ℕ} {dbs : DatabaseSchema} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R rn t).schema = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft}.toFinset := by ext a; simp

@[simp]
theorem BoundedQuery.schema.tEq_def {n : ℕ} (q : BoundedQuery dbs n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq q t₁ t₂).schema = q.schema ∪ t₁.varFinsetLeft ∪ t₂.varFinsetLeft := by simp_all [schema]

@[simp]
theorem BoundedQuery.schema.and_def {n : ℕ} (q₁ q₂ : BoundedQuery dbs n) :
  (and q₁ q₂).schema = q₁.schema ∪ q₂.schema := by simp_all [schema]

@[simp]
theorem BoundedQuery.schema.ex_def {n : ℕ} (q : BoundedQuery dbs (n + 1)) :
  (ex q).schema = q.schema := by simp_all [schema]

@[simp]
theorem BoundedQuery.schema.or_def {n : ℕ} (q₁ q₂ : BoundedQuery dbs n) :
  (or q₁ q₂).schema = q₁.schema ∪ q₂.schema := by simp_all [schema]

@[simp]
theorem BoundedQuery.schema.not_def {n : ℕ} (q : BoundedQuery dbs n) :
  (not q).schema = q.schema := by simp_all [schema]

@[simp]
theorem BoundedQuery.schema.exs_def {n : ℕ} (q : BoundedQuery dbs n) :
  (exs q).schema = q.schema := by
    induction n with
    | zero => rfl
    | succ n' ih => simp [ih q.ex, schema]
