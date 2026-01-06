import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.Equivalence.FOLtoRA.FreshAtts
import RelationalAlgebra.FOL.ModelTheoryExtensions

/-
The current FOLtoRA conversion does not support converting a relation with an empty schema.
To complete our proof, we put in place the assumption of not dealing with any of these relations.
Although this conversion could be done using `EmptyTupleFromRelation` from `Adom.lean`, it would require more setup and proof changes.
However, due to deadlines we decided to leave this change and the corresponding proof as future work
-/

open FOL FirstOrder Language Term RM

namespace FOL

/-- Whether all relations in the formula have a nonempty schema. -/
@[simp]
def NonemptyR {dbs : String → Finset String} : (fol dbs).BoundedFormula String n → Prop
  | .falsum => True
  | .rel R _ => match R with | .R rn => (dbs rn) ≠ ∅
  | .equal _ _ => True
  | .imp f₁ f₂ => NonemptyR f₁ ∧ NonemptyR f₂
  | .all f' => NonemptyR f'


/- Helper theorems for the `NonemptyR` property. -/
@[simp]
theorem NonemptyR.castLE {m n} (φ : (fol dbs).BoundedFormula String m) (h : m = n) {h' : m ≤ n} :
  NonemptyR (φ.castLE h') ↔ NonemptyR φ := by
    induction φ with
    | all f ih =>
      rename_i k
      subst h
      simp only [BoundedFormula.castLE, BoundedFormula.castLE_rfl, NonemptyR]
    | rel =>
      subst h
      simp_all only [BoundedFormula.castLE, Fin.castLE_rfl, Sum.map_id_id, relabel_id_eq_id, Function.id_comp,
        NonemptyR]
    | _ => simp_all

@[simp]
theorem NonemptyR.liftAt {n n'} (φ : (fol dbs).BoundedFormula String n) (hmn : m + n' ≤ n + 1) :
  NonemptyR (φ.liftAt n' m) ↔ NonemptyR φ := by
    rw [BoundedFormula.liftAt]
    induction φ with
    | all f ih =>
      rename_i k
      have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
      simp only [BoundedFormula.mapTermRel, NonemptyR, NonemptyR.castLE ?_ h, ih (hmn.trans k.succ.le_succ)]
    | rel R ts =>
      simp_all [BoundedFormula.mapTermRel, Term.liftAt]
      cases R with
      | R rn =>
        simp_all only
    | _ => simp_all [BoundedFormula.mapTermRel, Term.liftAt]; try grind

theorem NonemptyR.toPrenexImpRight {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsQF) (hψ : ψ.IsPrenex) :
    NonemptyR (φ.toPrenexImpRight ψ) ↔ NonemptyR (φ.imp ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [NonemptyR]
    rw [NonemptyR.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ
  | ex _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [NonemptyR]
    rw [NonemptyR.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ

theorem NonemptyR.toPrenexImp {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsPrenex) (hψ : ψ.IsPrenex) :
    NonemptyR (φ.toPrenexImp ψ) ↔ NonemptyR (φ.imp ψ) := by
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
    simp_all only [NonemptyR, and_true]

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
theorem NonemptyR.toPrenex (φ : (fol dbs).BoundedFormula String n) :
    NonemptyR φ.toPrenex ↔ NonemptyR φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp f1 f2 h1 h2 =>
    rw [BoundedFormula.toPrenex, NonemptyR.toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex,
      NonemptyR, NonemptyR, h1, h2]
  | all _ h =>
    rw [NonemptyR, BoundedFormula.toPrenex, NonemptyR, h]
