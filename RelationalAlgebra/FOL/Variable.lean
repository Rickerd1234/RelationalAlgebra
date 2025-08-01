import RelationalAlgebra.FOL.ModelTheory

namespace FOL

open FirstOrder Language RM

def outVar {n: ℕ} (v: Attribute) : fol.Term (Attribute ⊕ Fin n) := Term.var (Sum.inl v)
def inVar {n: ℕ} (i: Fin n) : fol.Term (Attribute ⊕ Fin n) := Term.var (Sum.inr i)

def outVar? {n : ℕ} : (vt : fol.Term (Attribute ⊕ Fin n)) → Option Attribute
  | .var x => x.getLeft?
  | _ => none

def inVar? {n : ℕ} : (vt : fol.Term (Attribute ⊕ Fin n)) → Option (Fin n)
  | .var x => x.getRight?
  | _ => none

theorem outVar?.injective {n : ℕ} (a a' : fol.Term (Attribute ⊕ Fin n)) : ∀ b ∈ outVar? a, b ∈ outVar? a' → a = a' :=
    by
    intro b a_1 a_2
    simp_all only [Option.mem_def, outVar?]
    aesop
