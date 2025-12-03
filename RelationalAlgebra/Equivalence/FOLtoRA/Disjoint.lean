import RelationalAlgebra.Equivalence.FOLtoRA.FRan
import RelationalAlgebra.FOL.ModelTheoryExtensions

open FOL FirstOrder Language Term RM

namespace FOL

@[simp]
def disjointSchema {dbs : String → Finset String} (brs : Finset String) : (fol dbs).BoundedFormula String n → Prop
  | .falsum => True
  | .rel R ts => match R with | .R rn => (Finset.univ.biUnion λ i => (ts i).varFinsetLeft) ∩ (dbs rn) = ∅ ∧ brs ∩ dbs rn = ∅
  | .equal _ _ => True
  | .imp f₁ f₂ => disjointSchema brs f₁ ∧ disjointSchema brs f₂
  | .all f' => disjointSchema brs f'


@[simp]
theorem disjointSchema.castLE {m n} (φ : (fol dbs).BoundedFormula String m) (h : m = n) {h' : m ≤ n} :
  disjointSchema brs (φ.castLE h') ↔ disjointSchema brs φ := by
    induction φ with
    | all f ih =>
      rename_i k
      subst h
      simp only [BoundedFormula.castLE, BoundedFormula.castLE_rfl, disjointSchema]
    | rel =>
      subst h
      simp_all only [BoundedFormula.castLE, Fin.castLE_rfl, Sum.map_id_id, relabel_id_eq_id, Function.id_comp,
        disjointSchema]
    | _ => simp_all

@[simp]
theorem disjointSchema.liftAt {n n'} (φ : (fol dbs).BoundedFormula String n) (hmn : m + n' ≤ n + 1) :
  disjointSchema brs (φ.liftAt n' m) ↔ disjointSchema brs φ := by
    rw [BoundedFormula.liftAt]
    induction φ with
    | all f ih =>
      rename_i k
      have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
      simp only [BoundedFormula.mapTermRel, disjointSchema, disjointSchema.castLE ?_ h, ih (hmn.trans k.succ.le_succ)]
    | rel R ts =>
      simp_all [BoundedFormula.mapTermRel, Term.liftAt]
      cases R with
      | R rn =>
        simp_all only
        apply Iff.intro
        · intro ⟨left, right⟩
          apply And.intro ?_ right
          ext a
          simp_all only [fol.Term.relabel_varFinsetLeft_id, Finset.notMem_empty]
        · intro ⟨left, right⟩
          simp_all only [and_true]
          ext a
          simp_all only [fol.Term.relabel_varFinsetLeft_id, Finset.notMem_empty]
    | _ => simp_all [BoundedFormula.mapTermRel, Term.liftAt]; try grind

theorem disjointSchema.toPrenexImpRight {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsQF) (hψ : ψ.IsPrenex) :
    disjointSchema brs (φ.toPrenexImpRight ψ) ↔ disjointSchema brs (φ.imp ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [disjointSchema]
    rw [disjointSchema.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ
  | ex _ ih =>
    rw [@BoundedFormula.toPrenexImpRight.eq_def]
    simp
    rw [ih]
    simp only [disjointSchema]
    rw [disjointSchema.liftAt _ (by grind)]
    exact BoundedFormula.IsQF.liftAt hφ

theorem disjointSchema.toPrenexImp {φ ψ : (fol dbs).BoundedFormula String n} (hφ : φ.IsPrenex) (hψ : ψ.IsPrenex) :
    disjointSchema brs (φ.toPrenexImp ψ) ↔ disjointSchema brs (φ.imp ψ) := by
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
    simp_all only [disjointSchema, and_true]

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
theorem disjointSchema.toPrenex (φ : (fol dbs).BoundedFormula String n) :
    disjointSchema brs φ.toPrenex ↔ disjointSchema brs φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp f1 f2 h1 h2 =>
    rw [BoundedFormula.toPrenex, disjointSchema.toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex,
      disjointSchema, disjointSchema, h1, h2]
  | all _ h =>
    rw [disjointSchema, BoundedFormula.toPrenex, disjointSchema, h]
