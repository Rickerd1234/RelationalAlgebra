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
def BoundedQuery.schema {n : ℕ} : (q : BoundedQuery n) → Finset Attribute
  | .R dbs name vMap => (R dbs name vMap).toFormula.freeVarFinset
  | .tEq q _ _ => q.schema
  | .and q1 q2 => q1.schema ∪ q2.schema
  | .ex q => q.schema

@[simp]
theorem BoundedQuery.schema.R_def_mem [folStruc] {n : ℕ} {x : Attribute} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  x ∈ (R dbs rn t).schema ↔ ∃i : Fin (dbs rn).card, x ∈ (t i).varFinsetLeft := by
    simp_all only [schema, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

instance BoundedQuery.schema.R_fintype [folStruc] {rn} {dbs : DatabaseSchema} {t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  Fintype {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    apply Fintype.ofFinset ((BoundedQuery.R dbs rn t).schema)
    simp only [BoundedQuery.schema.R_def_mem, Set.mem_setOf_eq, implies_true]

@[simp]
theorem BoundedQuery.schema.R_def [folStruc] {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).schema = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft}.toFinset := by ext a; simp

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
