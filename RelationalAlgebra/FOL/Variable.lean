import RelationalAlgebra.FOL.ModelTheory

namespace FOL

open FirstOrder Language RM

variable {α : Type}

def outVar {n: ℕ} (v: α) : fol.Term (α ⊕ Fin n) := Term.var (Sum.inl v)

@[simp]
theorem outVar.def {n} (v : α) : (outVar v : fol.Term (α ⊕ Fin n)) = Term.var (Sum.inl v) := rfl

def inVar {n: ℕ} (i: Fin n) : fol.Term (α ⊕ Fin n) := Term.var (Sum.inr i)

@[simp]
theorem inVar.def {n : ℕ} (i: Fin n) : (inVar i : fol.Term (α ⊕ Fin n)) = Term.var (Sum.inr i) := rfl

def outVar? {n : ℕ} : (vt : fol.Term (α ⊕ Fin n)) → Option α
  | .var x => x.getLeft?
  | _ => none

def inVar? {n : ℕ} : (vt : fol.Term (α ⊕ Fin n)) → Option (Fin n)
  | .var x => x.getRight?
  | _ => none

theorem outVar?.injective {n : ℕ} (a a' : fol.Term (α ⊕ Fin n)) : ∀ b ∈ outVar? a, b ∈ outVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, outVar?]
    aesop
