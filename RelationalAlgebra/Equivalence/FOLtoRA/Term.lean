import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.ModelTheory
import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Variable
import RelationalAlgebra.Util.RenameFunc

open RM FOL FirstOrder Language

/--
Deterministically convert a FOL variable (`(fol dbs).Term (String ⊕ Fin n)`) to an attribute (`String`).
`brs` should be disjoint from the `String` FOL variables
-/
def TermtoAtt (brs : Finset String) : (fol dbs).Term (String ⊕ Fin n) → String
  | var (Sum.inl s) => s
  | var (Sum.inr i) => FreeMap n brs i
  | _ => default

@[simp]
def TermtoAtt.eq_iff {t₁ t₂ : (fol dbs).Term (String ⊕ Fin n)} {brs : Finset String} (h : n ≤ brs.card) (h' : (t₁.varFinsetLeft ∪ t₂.varFinsetLeft) ∩ FRan (FreeMap n brs) = ∅) :
  (TermtoAtt brs t₁) = (TermtoAtt brs t₂) ↔ t₁ = t₂ := by
    have h := FreeMap.inj_n h
    apply Iff.intro
    . intro h''
      have ⟨k₁, hk₁⟩ := Term.cases t₁
      have ⟨k₂, hk₂⟩ := Term.cases t₂
      subst hk₁ hk₂
      simp_all only [Term.var.injEq]
      cases k₁ with
      | inl val =>
        cases k₂ with
        | inl val_1 =>
          subst h''
          simp_all only [TermtoAtt]
        | inr val_2 =>
          subst h''
          simp_all only [reduceCtorEq, TermtoAtt]
          simp at h'
      | inr val_1 =>
        cases k₂ with
        | inl val =>
          subst h''
          simp_all only [reduceCtorEq, TermtoAtt]
          simp at h'
        | inr val_2 =>
          simp_all only [Sum.inr.injEq]
          exact h h''
    . exact congrArg (TermtoAtt brs)

/--
Map an attribute `ra` (part of the schema for relation `rn`) to the corresponding 'variable' used in the FOL variable assignment `ts`
Note: `ra` should be in schema `dbs rn`
-/
def renamer {dbs : String → Finset String} (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) (ra : String) : String :=
  ((RelationSchema.index? (dbs rn) ra).map (TermtoAtt brs ∘ ts)).getD (default)

theorem renamer.notMem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∉ dbs rn) :
  renamer ts brs ra = default := by
    rw [renamer, RelationSchema.index?_none.mpr h, Option.map_none, Option.getD_none]

theorem renamer.mem_def {dbs : String → Finset String} {ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)} (h : ra ∈ dbs rn) :
  renamer ts brs ra = (TermtoAtt brs ∘ ts) (RelationSchema.index h) := by
    have ⟨k, hk⟩ := RelationSchema.index?_isSome_eq_iff.mp (RelationSchema.index?_isSome.mpr h)
    rw [RelationSchema.index]
    simp_rw [renamer, hk, Option.map_some, Option.getD_some, Option.get]

/-- Rename function which swaps the original `ra` for `renamer ts brs ra` and vice versa -/
def renamePairFunc {dbs : String → Finset String} (ra : String) (ts : Fin (dbs rn).card → (fol dbs).Term (String ⊕ Fin n)) (brs : Finset String) : String → String :=
  renameFunc ra (renamer ts brs ra)
