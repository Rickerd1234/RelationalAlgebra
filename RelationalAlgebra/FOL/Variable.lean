import RelationalAlgebra.FOL.ModelTheory

namespace FOL

open FirstOrder Language RM

variable {α : Type}

/-- Helper definition used for a free variable, part of the 'output'. -/
def outVar {n: ℕ} (v: α) : (fol dbs).Term (α ⊕ Fin n) := Term.var (Sum.inl v)

@[simp]
theorem outVar.def {n} (v : α) : (outVar v : (fol dbs).Term (α ⊕ Fin n)) = Term.var (Sum.inl v) := rfl

/-- Helper definition used for a bound variable, not part of the 'output', bound to quantifier `∃` or `∀`. -/
def inVar {n: ℕ} (i: Fin n) : (fol dbs).Term (α ⊕ Fin n) := Term.var (Sum.inr i)

@[simp]
theorem inVar.def {n : ℕ} (i: Fin n) : (inVar i : (fol dbs).Term (α ⊕ Fin n)) = Term.var (Sum.inr i) := rfl

def outVar? {n : ℕ} : (vt : (fol dbs).Term (α ⊕ Fin n)) → Option α
  | .var x => x.getLeft?
  | _ => none

def inVar? {n : ℕ} : (vt : (fol dbs).Term (α ⊕ Fin n)) → Option (Fin n)
  | .var x => x.getRight?
  | _ => none

theorem outVar?.injective {n : ℕ} (a a' : (fol dbs).Term (α ⊕ Fin n)) : ∀ b ∈ outVar? a, b ∈ outVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, outVar?]
    aesop
