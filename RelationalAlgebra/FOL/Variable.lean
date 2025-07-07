import RelationalAlgebra.FOL.ModelTheory

namespace FOL

open FirstOrder Language

abbrev Variable := String

def outVar {n: ℕ} (v: Variable) : fol.Term (Variable ⊕ Fin n) := Term.var (Sum.inl v)
def inVar {n: ℕ} (i: Fin n) : fol.Term (Variable ⊕ Fin n) := Term.var (Sum.inr i)

def outVar? {n : ℕ} : (vt : fol.Term (Variable ⊕ Fin n)) → Option Variable
  | .var x => x.getLeft?
  | _ => none

def inVar? {n : ℕ} : (vt : fol.Term (Variable ⊕ Fin n)) → Option (Fin n)
  | .var x => x.getRight?
  | _ => none

theorem outVar?.injective {n : ℕ} (a a' : fol.Term (Variable ⊕ Fin n)) : ∀ b ∈ outVar? a, b ∈ outVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, outVar?]
    aesop
