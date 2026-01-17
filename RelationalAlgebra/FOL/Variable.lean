import RelationalAlgebra.FOL.ModelTheory

namespace FOL

open FirstOrder Language RM

variable {α : Type}

/-- Helper definition used for a free variable, part of the 'output'. -/
def freeVar {n: ℕ} (v : α) : (fol dbs).Term (α ⊕ Fin n) := Term.var (Sum.inl v)

@[simp]
theorem freeVar.def {n} (v : α) : (freeVar v : (fol dbs).Term (α ⊕ Fin n)) = Term.var (Sum.inl v) := rfl

/-- Helper definition used for a bound variable, not part of the 'output', bound to quantifier `∃` or `∀`. -/
def boundVar {n: ℕ} (i: Fin n) : (fol dbs).Term (α ⊕ Fin n) := Term.var (Sum.inr i)

@[simp]
theorem boundVar.def {n : ℕ} (i: Fin n) : (boundVar i : (fol dbs).Term (α ⊕ Fin n)) = Term.var (Sum.inr i) := rfl

def freeVar? {n : ℕ} : (vt : (fol dbs).Term (α ⊕ Fin n)) → Option α
  | .var x => x.getLeft?
  | _ => none

def boundVar? {n : ℕ} : (vt : (fol dbs).Term (α ⊕ Fin n)) → Option (Fin n)
  | .var x => x.getRight?
  | _ => none

theorem freeVar?.injective {n : ℕ} (a a' : (fol dbs).Term (α ⊕ Fin n)) : ∀ b ∈ freeVar? a, b ∈ freeVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, freeVar?]
    aesop
