import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.FreshAtts
import RelationalAlgebra.FOL.ModelTheoryExtensions

/-
To simplify the conversion and proof, we decided to allow for the assumption that the attributes used to represent the bound variables (`brs`)
  is disjoint from the named attributes used in any of the relations and from any of the free variables used in the query.
This assumption is a short-cut, given we use `FreshAtts` to generate `brs` which avoids these variables.
However, due to deadlines we decided to leave this proof as future work.
-/

open FOL FirstOrder Language Term RM

namespace FOL

/-- Whether `brs : Finset String` has no intersection with any free variables in the formula. -/
@[simp]
def disjointSchemaL {dbs : String → Finset String} (brs : Finset String) : (fol dbs).BoundedFormula String n → Prop
  | .falsum => True
  | .rel R ts => match R with | .R rn => (Finset.univ.biUnion λ i => (ts i).varFinsetLeft) ∩ (dbs rn) = ∅
  | .equal _ _ => True
  | .imp f₁ f₂ => disjointSchemaL brs f₁ ∧ disjointSchemaL brs f₂
  | .all f' => disjointSchemaL brs f'

/-- `brs` does not intersect with any relation schema nor any free variables in the formula.  -/
@[simp]
def disjointSchema {dbs : String → Finset String} (brs : Finset String) (q : (fol dbs).BoundedFormula String n): Prop :=
  disjointSchemaL brs q ∧ ∀rn, brs ∩ dbs rn = ∅


/- Helper theorems for the `disjointSchemaL` property. -/
@[simp]
theorem disjointSchemaL.castLE {m n} (φ : (fol dbs).BoundedFormula String m) (h : m = n) {h' : m ≤ n} :
  disjointSchemaL brs (φ.castLE h') ↔ disjointSchemaL brs φ := by
    induction φ with
    | all f ih =>
      rename_i k
      subst h
      simp only [BoundedFormula.castLE, BoundedFormula.castLE_rfl, disjointSchemaL]
    | rel =>
      subst h
      simp_all only [BoundedFormula.castLE, Fin.castLE_rfl, Sum.map_id_id, relabel_id_eq_id, Function.id_comp,
        disjointSchemaL]
    | _ => simp_all

@[simp]
theorem disjointSchemaL.liftAt {n n'} (φ : (fol dbs).BoundedFormula String n) (hmn : m + n' ≤ n + 1) :
  disjointSchemaL brs (φ.liftAt n' m) ↔ disjointSchemaL brs φ := by
    rw [BoundedFormula.liftAt]
    induction φ with
    | all f ih =>
      rename_i k
      have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
      simp only [BoundedFormula.mapTermRel, disjointSchemaL, disjointSchemaL.castLE ?_ h, ih (hmn.trans k.succ.le_succ)]
    | rel R ts =>
      simp_all [BoundedFormula.mapTermRel, Term.liftAt]
      cases R with
      | R rn =>
        simp_all only
        apply Iff.intro
        · intro h
          ext a
          simp_all only [fol.Term.relabel_varFinsetLeft_id, Finset.notMem_empty]
        · intro h
          ext a
          simp_all only [fol.Term.relabel_varFinsetLeft_id, Finset.notMem_empty]
    | _ => simp_all [BoundedFormula.mapTermRel, Term.liftAt]; try grind

theorem disjointSchemaL.toPrenexImpRight {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsQF) (hψ : ψ.IsPrenex) :
    disjointSchemaL brs (φ.toPrenexImpRight ψ) ↔ disjointSchemaL brs (φ.imp ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [disjointSchemaL]
    rw [disjointSchemaL.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ
  | ex _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [disjointSchemaL]
    rw [disjointSchemaL.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ

theorem disjointSchemaL.toPrenexImp {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsPrenex) (hψ : ψ.IsPrenex) :
    disjointSchemaL brs (φ.toPrenexImp ψ) ↔ disjointSchemaL brs (φ.imp ψ) := by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact toPrenexImpRight hφ hψ
  | all _ ih =>
    rename_i n' φ hφ
    intro ψ hψ
    rw [BoundedFormula.toPrenexImp]
    simp_all only [disjointSchemaL, and_true]

    have : (BoundedFormula.liftAt 1 n' ψ).IsPrenex := hψ.liftAt
    have := ih this
    simp at *
    exact this
  | ex _ ih =>
    rename_i n' φ hφ
    intro ψ hψ

    have : (BoundedFormula.liftAt 1 n' ψ).IsPrenex := hψ.liftAt
    have := ih this
    simp at *
    exact this

@[simp]
theorem disjointSchemaL.toPrenex (φ : (fol dbs).BoundedFormula String n) :
    disjointSchemaL brs φ.toPrenex ↔ disjointSchemaL brs φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp f1 f2 h1 h2 =>
    rw [BoundedFormula.toPrenex, disjointSchemaL.toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex,
      disjointSchemaL, disjointSchemaL, h1, h2]
  | all _ h =>
    rw [disjointSchemaL, BoundedFormula.toPrenex, disjointSchemaL, h]
