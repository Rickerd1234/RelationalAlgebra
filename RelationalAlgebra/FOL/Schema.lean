import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language RM Term

namespace FOL

-- Extend ModelTheory
@[simp]
theorem BoundedFormula.exs.freeVarFinset {k} (φ : (fol dbs).BoundedFormula String k) :
  (φ.exs).freeVarFinset = φ.freeVarFinset := by
    induction k
    . simp [BoundedFormula.exs]
    . simp [BoundedFormula.exs]
      simp_all only [BoundedFormula.freeVarFinset, Finset.union_empty]

def castLERS  [DecidableEq Attribute] (rs : Finset (Attribute ⊕ Fin n)) (h : n ≤ m) : Finset (Attribute ⊕ Fin m) :=
  Finset.image (Sum.map id (Fin.castLE h)) rs

@[simp]
def BoundedFormula.varFinset [DecidableEq Attribute] : (f : (fol dbs).BoundedFormula Attribute n) → Finset (Attribute ⊕ (Fin (n + depth f)))
  | .falsum => ∅
  | .rel R ts => Finset.univ.biUnion λ i => (ts i).varFinset
  | .equal t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | .imp f₁ f₂ => castLERS (varFinset f₁) (by simp) ∪ castLERS (varFinset f₂) (by simp)
  | .all f' => castLERS (varFinset f') (by simp only [depth]; grind only)

-- def ex_dbs : String → Finset String
--   | "R1" => {"a", "b", "c"}
--   | "R2" => {"d", "e", "f"}
--   | "R3" => {"a", "b", "d"}
--   | _ => ∅

-- #simp [BoundedFormula.varFinset] BoundedFormula.varFinset (.falsum (α := String) (n := 0) (L := fol ex_dbs))
-- #simp [BoundedFormula.varFinset, ex_dbs] BoundedFormula.varFinset (.rel (.R "R2") ([outVar "b", outVar "c", inVar 0].get) (α := String) (n := 1) (L := fol ex_dbs))
-- #simp [BoundedFormula.varFinset] BoundedFormula.varFinset (.equal (outVar "a") (inVar 0) (n := 1) (L := fol ex_dbs))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.imp (.equal (outVar "a") (inVar 0)) (.equal (outVar "b") (inVar 1)) (n := 2) (L := fol ex_dbs))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.all (.equal (outVar "a") (inVar 0)) (n := 0) (L := fol ex_dbs))
-- #simp [BoundedFormula.varFinset, castLERS] BoundedFormula.varFinset (.all (.imp (.all (.equal (outVar "a") (inVar 1))) (.all (.equal (outVar "b") (inVar 1)))) (n := 0) (L := fol ex_dbs))

-- schema of query
def BoundedQuery.schema {n : ℕ} (q : BoundedQuery dbs n) : Finset String :=
  q.toFormula.freeVarFinset

@[simp]
theorem BoundedQuery.schema.R_def_mem {n : ℕ} {x : String} {dbs : String → Finset String} (t : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) :
  x ∈ (R rn t).schema ↔ ∃i : Fin (dbs rn).card, x ∈ (t i).varFinsetLeft := by
    simp_all only [schema, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

instance BoundedQuery.schema.R_fintype {rn} {dbs : String → Finset String} {t : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} :
  Fintype {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    apply Fintype.ofFinset ((BoundedQuery.R rn t).schema)
    simp only [BoundedQuery.schema.R_def_mem, Set.mem_setOf_eq, implies_true]

@[simp]
theorem BoundedQuery.schema.R_def {n : ℕ} {dbs : String → Finset String} (t : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) :
  (R rn t).schema = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft}.toFinset := by ext a; simp

@[simp]
theorem BoundedQuery.schema.tEq_def {n : ℕ} (t₁ t₂ : (fol dbs).Term (String ⊕ Fin n)) :
  (tEq t₁ t₂ : BoundedQuery dbs n).schema = t₁.varFinsetLeft ∪ t₂.varFinsetLeft := by simp_all [schema]

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
    | succ n' ih => simp [schema]
