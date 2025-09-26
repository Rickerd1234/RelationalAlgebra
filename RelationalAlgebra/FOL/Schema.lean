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

def BoundedQuery.hasSafeTerm {n : ℕ} (t : fol.Term (Attribute ⊕ Fin n)) : (q : BoundedQuery n) → Prop
  | .R _ _ vMap => ∃i, (vMap i) = t
  | .tEq q _ _ => q.hasSafeTerm t
  | .and q1 q2 => q1.hasSafeTerm t ∨ q2.hasSafeTerm t
  | .ex q => q.hasSafeTerm (t.relabel (Sum.map id (Fin.castLE (Nat.le_add_right n 1))))
  | .or q1 q2 => q1.hasSafeTerm t ∨ q2.hasSafeTerm t
  | .not q => q.hasSafeTerm t


@[simp]
theorem BoundedQuery.hasSafeTerm.R_def {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) (t' : fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).hasSafeTerm t' = ∃i, (t i) = t' := by rfl

@[simp]
theorem BoundedQuery.hasSafeTerm.tEq_def {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) (t' : fol.Term (Attribute ⊕ Fin n))  :
  (tEq q t₁ t₂).hasSafeTerm t' = q.hasSafeTerm t' := by rfl

@[simp]
theorem BoundedQuery.hasSafeTerm.and_def {n : ℕ} (q₁ q₂ : BoundedQuery n) (t' : fol.Term (Attribute ⊕ Fin n)) :
  (and q₁ q₂).hasSafeTerm t' = (q₁.hasSafeTerm t' ∨ q₂.hasSafeTerm t') := by rfl

@[simp]
theorem BoundedQuery.hasSafeTerm.ex_def {n : ℕ} (q : BoundedQuery (n + 1)) (t' : fol.Term (Attribute ⊕ Fin n)) :
  (ex q).hasSafeTerm t' = q.hasSafeTerm (t'.relabel (Sum.map id (Fin.castLE (Nat.le_add_right n 1)))) := by rfl

@[simp]
theorem BoundedQuery.hasSafeTerm.or_def {n : ℕ} (q₁ q₂ : BoundedQuery n) (t' : fol.Term (Attribute ⊕ Fin n)) :
  (or q₁ q₂).hasSafeTerm t' = (q₁.hasSafeTerm t' ∨ q₂.hasSafeTerm t') := by rfl

@[simp]
theorem BoundedQuery.hasSafeTerm.not_def {n : ℕ} (q : BoundedQuery n) (t' : fol.Term (Attribute ⊕ Fin n)) :
  (not q).hasSafeTerm t' = q.hasSafeTerm t' := by rfl

-- schema of query
def BoundedQuery.schema {n : ℕ} : (q : BoundedQuery n) → Finset Attribute
  | .R dbs name vMap => (R dbs name vMap).toFormula.freeVarFinset
  | .tEq q _ _ => q.schema
  | .and q1 q2 => q1.schema ∪ q2.schema
  | .ex q => q.schema
  | .or q1 q2 => q1.schema ∪ q2.schema
  | .not q => q.schema

@[simp]
theorem BoundedQuery.schema.R_def_mem {n : ℕ} {x : Attribute} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  x ∈ (R dbs rn t).schema ↔ ∃i : Fin (dbs rn).card, x ∈ (t i).varFinsetLeft := by
    simp_all only [schema, toFormula, Relations.boundedFormula,
      BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

instance BoundedQuery.schema.R_fintype {rn} {dbs : DatabaseSchema} {t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} :
  Fintype {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft} := by
    apply Fintype.ofFinset ((BoundedQuery.R dbs rn t).schema)
    simp only [BoundedQuery.schema.R_def_mem, Set.mem_setOf_eq, implies_true]

@[simp]
theorem BoundedQuery.schema.R_def {n : ℕ} (t : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)) :
  (R dbs rn t).schema = {a | ∃i : Fin (dbs rn).card, a ∈ (t i).varFinsetLeft}.toFinset := by ext a; simp

@[simp]
theorem BoundedQuery.schema.tEq_def {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) :
  (tEq q t₁ t₂).schema = q.schema := rfl

@[simp]
theorem BoundedQuery.schema.and_def {n : ℕ} (q₁ q₂ : BoundedQuery n) :
  (and q₁ q₂).schema = q₁.schema ∪ q₂.schema := rfl

@[simp]
theorem BoundedQuery.schema.ex_def {n : ℕ} (q : BoundedQuery (n + 1)) :
  (ex q).schema = q.schema := rfl

@[simp]
theorem BoundedQuery.schema.or_def {n : ℕ} (q₁ q₂ : BoundedQuery n) :
  (or q₁ q₂).schema = q₁.schema ∪ q₂.schema := rfl

@[simp]
theorem BoundedQuery.schema.not_def {n : ℕ} (q : BoundedQuery n) :
  (not q).schema = q.schema := rfl

@[simp]
theorem BoundedQuery.schema.exs_def {n : ℕ} (q : BoundedQuery n) :
  (exs q).schema = q.schema := by
    induction n with
    | zero => rfl
    | succ n' ih => exact ih q.ex

-- Some theorems to connect schema and hasSafeTerm
@[simp]
theorem BoundedQuery.hasSafeTerm_mem_schema (q : BoundedQuery n) :
  q.hasSafeTerm (var (Sum.inl a)) ↔ a ∈ q.schema := by
    induction q with
    | R dbs rn t =>
      rename_i n'
      simp_all only [hasSafeTerm.R_def, schema.R_def, Set.mem_toFinset, Set.mem_setOf_eq]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        use w
        simp_all only [varFinsetLeft.eq_1, Finset.mem_singleton]
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        use w
        have ⟨t', ht'⟩ := Term.cases (t w)
        simp_all only [var.injEq]
        cases t' with
        | inl val => simp_all only [varFinsetLeft, Finset.mem_singleton]
        | inr val_1 => simp_all only [varFinsetLeft, Finset.not_mem_empty]

    | _ => simp_all
